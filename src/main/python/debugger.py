#!/usr/bin/env python
# -*- coding: utf-8 -*-
import curses
import sys
import time

class Debug:
    def __init__(self, indent_level):
        self.__objects = []
        self.__text = ""
        self.__expanded = False
        self.__indent_level = indent_level
        self.__cached_str = None
        self.__cached_node_count = 0
        pass

    def add(self, object):
        self.__objects.append(object)
        self.__cached_str = None

    def setText(self, text):
        self.__text = text
        self.__cached_str = None

    def lines(self):
        retv = [self]
        if (self.__expanded):
            retv += [line for o in self.__objects for line in o.lines()]
        return retv

    def expand(self):
        self.__expanded = True

    def collapse(self):
        self.__expanded = False

    def isExpandable(self):
        return self.__objects != []

    def isExpanded(self):
        return self.__expanded

    def indentLevel(self):
        return self.__indent_level

    def text(self):
        return self.__text

    def updateNodeCount(self):
        self.__cached_node_count = 1
        for o in self.__objects:
            o.updateNodeCount()
            self.__cached_node_count += o.nodeCount()
    def nodeCount(self):
        return self.__cached_node_count

    def __textChunks(self, chunks):
        chunks.append(self.__text)
        for o in self.__objects:
            o.__textChunks(chunks)
        return chunks

    def __str__(self):
        return "".join(self.__textChunks([]))

def parseLineChunks(
        line, previous, parsed_line, split_at_comma, position, indent_level):
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
    return line.startswith("starting ")

def endsLevel(line):
    return line.startswith("ending ")

def readDebug(debug, it, indent_level):
    dropThing = False
    while True:
        try:
            line = next(it)
        except StopIteration:
            break
        line_debug = parseLine(line, indent_level)
        if startsLevel(line):
            childLine = readDebug(line_debug, it, indent_level + 1)
            if " D_Step " in line:
                line_debug.expand()
            if not (childLine is None):
                debug.add(childLine)
            continue
        debug.add(line_debug)
        if endsLevel(line):
            dropThing = line.endswith("result: ()")
            break
    if dropThing:
        return None
    return debug

class LineAttributes:
    def __init__(self,
            is_selected, is_expanded, is_expandable, indent_level, node_count):
        self.is_selected = is_selected
        self.is_expanded = is_expanded
        self.is_expandable = is_expandable
        self.indent_level = indent_level
        self.node_count = node_count

class WindowState:
    def __init__(self, debug):
        self.__debug = debug
        self.__first_window_line = 0
        self.__selected_line = 0

    def lines(self, y):
        line_index = 0
        for line in self.__debug.lines():
            window_line = line_index - self.__first_window_line
            if window_line >= 0:
                if window_line >= y:
                    break
                yield (
                    LineAttributes(
                        is_selected = line_index == self.__selected_line,
                        is_expanded = line.isExpanded(),
                        is_expandable = line.isExpandable(),
                        indent_level = line.indentLevel(),
                        node_count = line.nodeCount()),
                    line.text())
            line_index += 1

    def up(self):
        if self.__selected_line <= 0:
            return
        self.__selected_line -= 1
        self.__first_window_line = min(
            self.__selected_line, self.__first_window_line)

    def pg_up(self, y):
        self.__selected_line -= y - 1
        if self.__selected_line <= 0:
            self.__selected_line = 0
        self.__first_window_line = min(
            self.__selected_line, self.__first_window_line)

    def down(self):
        if self.__selected_line >= len(self.__debug.lines()) - 1:
            return
        self.__selected_line += 1

    def pg_down(self, y):
        self.__selected_line += y - 1
        if self.__selected_line >= len(self.__debug.lines()) - 1:
            self.__selected_line = len(self.__debug.lines()) - 1

    def home(self):
        self.__selected_line = 0
        self.__first_window_line = 0

    def end(self):
        self.__selected_line = len(self.__debug.lines()) - 1

    def expand(self):
        self.__debug.lines()[self.__selected_line].expand()

    def collapse(self):
        self.__debug.lines()[self.__selected_line].collapse()


    def updateHeight(self, y):
        if self.__selected_line - self.__first_window_line >= y:
            self.__first_window_line = self.__selected_line - (y - 1)/2

class WindowPainter:
    def __init__(self, window):
        self.__window = window

    def paint(self, state):
        (y, x) = self.__window.getmaxyx()
        state.updateHeight(y)
        self.__window.erase()
        window_line = 0
        for (line_attrs, line) in state.lines(y):
            assert window_line >= 0
            assert window_line < y
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
        line = (
            prefix
            + ("#nc=%d: " % line_attrs.node_count)
            + line
            + (' ' * max_x)
            )[:max_x - 1]
        self.__window.addstr(y, 0, line, attr)

def main(args):
    sys.setrecursionlimit(5000)
    with open(args[0]) as f:
        debug = readDebug(
            Debug(0),
            iter([l[ : len(l) - 1] for l in f.readlines()]),
            0)
        debug.expand()
        print "*"
        debug.updateNodeCount()

    try:
        window = curses.initscr()
        curses.noecho()
        curses.cbreak()
        window.keypad(True)

        window_state = WindowState(debug)
        window_painter = WindowPainter(window)
        (x, y) = window.getmaxyx()

        while True:
            (x, y) = window.getmaxyx()
            window_painter.paint(window_state)
            key = window.getch()
            if key == ord('q'):
                break
            elif key == curses.KEY_UP:
                window_state.up()
            elif key == curses.KEY_DOWN:
                window_state.down()
            elif key == curses.KEY_PPAGE:
                window_state.pg_up(y)
            elif key == curses.KEY_NPAGE:
                window_state.pg_down(y)
            elif key == curses.KEY_RIGHT:
                window_state.expand()
            elif key == curses.KEY_LEFT:
                window_state.collapse()
            elif key == curses.KEY_END:
                window_state.end()
            elif key == curses.KEY_HOME:
                window_state.home()
    finally:
        curses.nocbreak()
        curses.echo()
        window.keypad(False)
        curses.endwin()

    print x, y


if __name__ == "__main__":
    main(sys.argv[1:])
