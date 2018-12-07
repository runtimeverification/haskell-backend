#!/usr/bin/env python
# -*- coding: utf-8 -*-

"""
Interactive debugging tool for kore.

Usage, part 1:
1. Run the program, preferably instrumented with the Kore.Debug functions.
2. Pipe the output through debugFilter.py and write the result to a file.
3. Run debugger.py with the result file as an argument.

Example:

cd src/main/k/working/imp
../../../../../.build/k/k-distribution/bin/kprove \
    --haskell-backend-command "stack exec kore-exec --" \
    tests/sum-spec.k \
    --depth 9 \
    2>&1 | ../../../python/debugFilter.py onlyfilter > debug
../../../python/debugger.py debug

Usage, part 2:

'q' quits the debugger.

The 'up', 'down', 'home' and 'end' keys move through the list of displayed
lines. 'PgUp' and 'PgDown' may be added at a later time.

Lines having a "+" at the beginning can be expanded with the 'right' key and
lines having a "-" can be collapsed with the 'left' key.

"""

import curses
import sys
import time

class Debug:
    """A node in the parsed debug tree.

    Consists of a title and some children. If it has children, then it can be
    expanded and collapsed.

    It also has an indentation level which usually corresponds to its depth
    in the debug tree.
    """
    def __init__(self, indent_level):
        self.__objects = []
        self.__text = ""
        self.__expanded = False
        self.__indent_level = indent_level
        self.__cached_str = None
        pass

    def add(self, object):
        """Adds a child to this node.

        TODO: Move 'add' and 'setText' to a 'Builder' object.
        """
        self.__objects.append(object)
        self.__cached_str = None

    def setText(self, text):
        """Sets the title of this node."""
        self.__text = text
        self.__cached_str = None

    def lines(self):
        """Returns a list of visible descendants in order.

        It does not return descendants of unexpanded nodes.
        """
        retv = [self]
        if (self.__expanded):
            retv += [line for o in self.__objects for line in o.lines()]
        return retv

    def expand(self):
        """Marks the current node as 'expanded'."""
        self.__expanded = True

    def collapse(self):
        """Marks the current node as 'not expanded'."""
        self.__expanded = False

    def isExpandable(self):
        """Whether the current node could ever be expanded."""
        return self.__objects != []

    def isExpanded(self):
        """Whether the current node is currently expanded."""
        return self.__expanded

    def indentLevel(self):
        """Returns the indent level given at creation time."""
        return self.__indent_level

    def text(self):
        """Returns the title."""
        return self.__text

    def __textChunks(self, chunks):
        chunks.append(self.__text)
        for o in self.__objects:
            o.__textChunks(chunks)
        return chunks

    def __str__(self):
        return "".join(self.__textChunks([]))

def parseLineChunks(
        line, previous, parsed_line, split_at_comma, position, indent_level):
    """Adds the debug tree starting at the given position to parsed_line.

    See the 'parseLine' documentation for details.
    """
    while position < len(line):
        if line[position] in "([{":
            if previous < position:
                parsed = Debug(indent_level)
                parsed.setText(line[previous:position])
                parsed_line.add(parsed)

            while position < len(line) and line[position] in "([{,":
                parsed_start = position
                parsed = Debug(indent_level + 1)
                position = parseLineChunks(
                    line,
                    previous = position,
                    parsed_line = parsed,
                    split_at_comma = True,
                    position = position + 1,
                    indent_level = indent_level + 1)
                parsed.setText(line[parsed_start:position])
                parsed_line.add(parsed)

            if position >= len(line):
                return position
            assert line[position] in '}])'

            parsed = Debug(indent_level + 1)
            parsed.setText(line[position])
            parsed_line.add(parsed)

            position += 1
            previous = position
            continue
        elif (line[position] in "}])"
                or (line[position] == "," and split_at_comma)):
            if previous < position - 1:
                parsed = Debug(indent_level)
                parsed.setText(line[previous:position - 1])
                parsed_line.add(parsed)
            return position
        else:
            position += 1
    if previous < position:
        parsed = Debug(indent_level)
        parsed.setText(line[previous:position])
        parsed_line.add(parsed)
    return position

def parseLine(line, indent_level):
    """Creates a debug tree from the given parsed line.

    It assumes that the line contains a correctly parenthesised term.
    It allows one exception, some of the closing parenthesis may
    be missing at the end of the string.

    The input line is a list of strings that, when concatenated, produce
    the debug text. Parentheses and commas are assumed to be separate
    strings, and the should not be any consecutive element that are
    not parentheses and commas, e.g.

    ["function ", "(", "arg1", ",", " arg2", ")"]

    is correct, but the following are not:

    ["my", "function ", "(", "arg1", ",", " arg2", ")"]
    "my" and "function" are consecutive non-delimiter elements.

    ["function ", "(", "arg1", ", ", "arg2", ")"]
    the comma between args is not a separate string, it also contains a space.

    In general, an inner parsed object will end with one of the following:
    1. If it contains parentheses:
    1.a. Its closing parenthesis.
    1.b. The end of the string.
    2. If the parsed object does not contain parentheses:
    2.a. Any closing parenthesis.
    2.b. The first comma, except on the first tree level.
    2.c. The end of the string.
    """
    parsed = Debug(indent_level)
    parsed.setText(line)
    parseLineChunks(
        line,
        previous = 0,
        parsed_line = parsed,
        split_at_comma = False,
        position = 0,
        indent_level = indent_level + 2)
    return parsed

def startsLevel(line):
    """Identifies the start of an input section.

    See 'readDebug' for details.
    """
    return line.startswith("starting ")

def endsLevel(line):
    """Identifies the end of an input section.

    See 'readDebug' for details.
    """
    return line.startswith("ending ")

def readDebug(debug, it, indent_level):
    """Reads the contents of an input section.

    An entire section will be represented as a debug tree node, with
    the starting line as the root and all the other lines, including the
    section ending lines, as children.
    """
    while True:
        try:
            line = next(it)
        except StopIteration:
            break
        line_debug = parseLine(line, indent_level)
        if startsLevel(line):
            debug.add(readDebug(line_debug, it, indent_level + 1))
            continue
        debug.add(line_debug)
        if endsLevel(line):
            break
    return debug

class LineAttributes:
    """Meta-information needed for displaying a debug node."""
    def __init__(self, is_selected, is_expanded, is_expandable, indent_level):
        self.is_selected = is_selected
        self.is_expanded = is_expanded
        self.is_expandable = is_expandable
        self.indent_level = indent_level

class WindowState:
    """Interface for displaying a debug tree."""
    def __init__(self, debug):
        self.__debug = debug
        self.__first_window_line = 0
        self.__selected_line = 0

    def lines(self, window_height):
        """Transforms a tree into lines that can be displayed.

        Each visible node is a 'line'. Visible refers both to "within the
        current window" and to "accessible through expanded nodes".

        Returns an iterator over (metadata, debug-tree-node) pairs.
        """
        line_index = 0
        for line in self.__debug.lines():
            window_line = line_index - self.__first_window_line
            if window_line >= 0:
                if window_line >= window_height:
                    break
                yield (
                    LineAttributes(
                        is_selected = line_index == self.__selected_line,
                        is_expanded = line.isExpanded(),
                        is_expandable = line.isExpandable(),
                        indent_level = line.indentLevel()),
                    line.text())
            line_index += 1

    def previousLine(self):
        """Moves the cursor to the previous line."""
        if self.__selected_line <= 0:
            return
        self.__selected_line -= 1
        self.__first_window_line = min(
            self.__selected_line, self.__first_window_line)

    def nextLine(self):
        """Moves the cursor to the next line."""
        if self.__selected_line >= len(self.__debug.lines()) - 1:
            return
        self.__selected_line += 1

    def firstLine(self):
        """Moves the cursor to the first line."""
        self.__selected_line = 0
        self.__first_window_line = 0

    def lastLine(self):
        """Moves the cursor to the last line."""
        self.__selected_line = len(self.__debug.lines()) - 1

    def expand(self):
        """Expands the current line/debug tree node."""
        self.__debug.lines()[self.__selected_line].expand()

    def collapse(self):
        """Collapses the current line/debug tree node."""
        self.__debug.lines()[self.__selected_line].collapse()

    def updateHeight(self, window_height):
        """Updates the internal state so that it makes sense within window_height."""
        if self.__selected_line - self.__first_window_line - 1 >= window_height:
            self.__first_window_line =
                self.__selected_line - (window_height - 1)/2

class WindowPainter:
    """Handles all the details of actually displaying debug information."""
    def __init__(self, window):
        self.__window = window

    def paint(self, state):
        """Paints the given window state.

        Before painting, it updates the state with the current window height.
        """
        (y, x) = self.__window.getmaxyx()
        state.updateHeight(y)
        self.__window.erase()
        window_line = 0
        for (line_attrs, line) in state.lines(y):
            self.__putLine(
                window_line, x, line, line_attrs)
            window_line += 1
        self.__window.refresh()

    def __putLine(self, y, max_x, line, line_attrs):
        if line_attrs.is_selected:
            attr = curses.A_REVERSE
        else:
            attr = curses.A_NORMAL
        if line_attrs.is_expandable:
            if line_attrs.is_expanded:
                prefix = "- "
            else:
                prefix = "+ "
        else:
            prefix = "| "
        prefix += "| " * line_attrs.indent_level
        line = (prefix + line + (' ' * max_x))[:max_x - 1]
        self.__window.addstr(y, 0, line, attr)

def main(args):
    try:
        window = curses.initscr()
        curses.noecho()
        curses.cbreak()
        window.keypad(True)

        with open(args[0]) as f:
            debug = readDebug(
                Debug(0),
                iter([l[ : len(l) - 1] for l in f.readlines()]),
                0)
            debug.expand()

        window_state = WindowState(debug)
        window_painter = WindowPainter(window)
        (x, y) = window.getmaxyx()

        while True:
            window_painter.paint(window_state)
            key = window.getch()
            if key == ord('q'):
                break
            elif key == curses.KEY_UP:
                window_state.previousLine()
            elif key == curses.KEY_DOWN:
                window_state.nextLine()
            elif key == curses.KEY_RIGHT:
                window_state.expand()
            elif key == curses.KEY_LEFT:
                window_state.collapse()
            elif key == curses.KEY_END:
                window_state.lastLine()
            elif key == curses.KEY_HOME:
                window_state.firstLine()
    finally:
        curses.nocbreak()
        curses.echo()
        window.keypad(False)
        curses.endwin()

    print x, y


if __name__ == "__main__":
    main(sys.argv[1:])
