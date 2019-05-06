#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Lint haskell files. Sample invocations:
#
# src/main/python/lint.py ./kore/src/Kore/Parser/Parser.hs
#
# for f in `find ./kore -name '*.hs'`; do src/main/python/lint.py $f; done
#
# for f in `find ./kore -name '*.hs-boot'`; do src/main/python/lint.py $f; done
#
import io
import sys

class OnlyOnce:
    """
    Runs an action only the first time run() is called.
    """
    def __init__(self, action):
        self.__action = action

    def run(self):
        if not (self.__action is None):
            self.__action()
            self.__action = None

def show(thing):
    """
    Wrapper for print to make it easier to use in lambdas.
    """
    print thing

class FileProcessor:
    """
    Finite automata for finding errors in a haskell file.
    """
    START = 0
    START_ALPHANUM = 1
    MINUS = 2
    MINUSMINUS = 3
    CURLYBRACE = 4
    SINGLE_LINE_COMMENT = 5
    MULTILINE_COMMENT_START = 6
    MULTILINE_COMMENT = 7
    MULTILINE_COMMENT_PRAGMA = 8
    MULTILINE_COMMENT_MINUS = 9
    MULTILINE_COMMENT_PRAGMA_MINUS = 10
    STRING = 11
    STRING_QUOTE = 12
    STRING_MULTILINE = 13
    CHAR = 14
    CHAR_QUOTE = 15

    SUBSTATE_START_NEW = 1
    SUBSTATE_START_MIDDLE = 2
    SUBSTATE_START_I = 3
    SUBSTATE_START_IM = 4
    SUBSTATE_START_IMP = 5
    SUBSTATE_START_IMPO = 6
    SUBSTATE_START_IMPOR = 7
    SUBSTATE_START_IMPORT = 8
    SUBSTATE_START_IMPORT_SPACE = 9
    SUBSTATE_START_IMPORT_SPACE_NEW = 10

    SUBSTATE_COMMENT_NEW = 1
    SUBSTATE_COMMENT_MIDDLE = 2
    SUBSTATE_COMMENT_H = 3
    SUBSTATE_COMMENT_HT = 4
    SUBSTATE_COMMENT_HTT = 5
    SUBSTATE_COMMENT_HTTP = 6

    def __init__(self, name):
        self.__name_printer = OnlyOnce(lambda: (show("Warnings in %s:" % name)))
        self.__name = name
        self.__state = FileProcessor.START
        self.__substate = FileProcessor.SUBSTATE_START_NEW
        self.__error_count = 0

        self.__comment_exceptions = [ "kore/src/Kore/Parser/Parser.hs" ]
        self.__full_exceptions = [ "kore/test/Test" ]

    def error_count(self):
        return self.__error_count

    def processLine(self, line_number, line):
        """
        Processes a single file line.

        Preserves context between lines.
        """
        if self.__isFullException():
            return
        length_error = OnlyOnce(
            lambda: (self.__error80Chars(line_number)))
        char_number = 0
        for char in line:
            char_number += 1
            self.__processChar(length_error, char_number, char)
        self.__procesEndOfLine()

    def __processChar(self, length_error, char_number, char):
        start_state = self.__state
        start_substate = self.__substate
        self.__updateState(char)
        #print (start_state, start_substate), "+", [char], "->", (self.__state, self.__substate)
        self.__checkForErrors(
            char_number,
            length_error,
            start_state,
            start_substate)

    def __checkForErrors(
            self, char_number, length_error, start_state, start_substate):
        pragma_comments = [
            FileProcessor.MULTILINE_COMMENT_PRAGMA,
            FileProcessor.MULTILINE_COMMENT_PRAGMA_MINUS]
        if char_number > 80:
            if (self.__state == FileProcessor.START
                    or self.__state == FileProcessor.START_ALPHANUM):
                if self.__substate == FileProcessor.SUBSTATE_START_IMPORT_SPACE:
                    return
            if self.__state in [
                    FileProcessor.SINGLE_LINE_COMMENT,
                    FileProcessor.MULTILINE_COMMENT_START,
                    FileProcessor.MULTILINE_COMMENT,
                    FileProcessor.MULTILINE_COMMENT_MINUS]:
                if self.__substate == FileProcessor.SUBSTATE_COMMENT_HTTP:
                    return
                if self.__isCommentException():
                    return
            if (self.__state in pragma_comments
                    or start_state in pragma_comments):
                return
            length_error.run()
            return
        return

    def __isCommentException(self):
        for exception in self.__comment_exceptions:
            if exception in self.__name:
                return True
        return False

    def __isFullException(self):
        for exception in self.__full_exceptions:
            if exception in self.__name:
                return True
        return False

    def __updateState(self, char):
        if ( self.__state == FileProcessor.START
                or self.__state == FileProcessor.START_ALPHANUM):
            if char == '-':
                self.__state = FileProcessor.MINUS
            elif char == '{':
                self.__state = FileProcessor.CURLYBRACE
            elif char == '"':
                self.__state = FileProcessor.STRING
            elif char == "'" and self.__state != FileProcessor.START_ALPHANUM:
                self.__state = FileProcessor.CHAR
            else:
                if char.isalnum() or char == "'":
                    self.__state = FileProcessor.START_ALPHANUM
                else:
                    self.__state = FileProcessor.START
                self.__updateStartSubstate(char)
        elif self.__state == FileProcessor.MINUS:
            if char == '-':
                self.__state = FileProcessor.MINUSMINUS
            elif char == '{':
                self.__state = FileProcessor.CURLYBRACE
            elif char == '"':
                self.__state = FileProcessor.STRING
            elif char == "'":
                self.__state = FileProcessor.CHAR
            else:
                self.__startState()
        elif self.__state == FileProcessor.MINUSMINUS:
            if char.isspace or char.isalnum() or char in "\"'{}()[]":
                self.__startSingleLineComment()
            elif char == '-':
                pass
            else:
                self.__startState()
        elif self.__state == FileProcessor.SINGLE_LINE_COMMENT:
            self.__updateCommentSubstate(char)
        elif self.__state == FileProcessor.CURLYBRACE:
            if char == "-":
                self.__startMultiLineComment()
            elif char == "{":
                pass
            elif char == '"':
                self.__state = FileProcessor.STRING
            elif char == "'":
                self.__state = FileProcessor.CHAR
            else:
                self.__startState()
        elif self.__state == FileProcessor.MULTILINE_COMMENT_START:
            if char == "-":
                self.__state = FileProcessor.MULTILINE_COMMENT_MINUS
                self.__updateCommentSubstate(char)
            elif char == "#":
                self.__state = FileProcessor.MULTILINE_COMMENT_PRAGMA
            else:
                self.__state = FileProcessor.MULTILINE_COMMENT
                self.__updateCommentSubstate(char)
        elif self.__state == FileProcessor.MULTILINE_COMMENT:
            if char == "-":
                self.__state = FileProcessor.MULTILINE_COMMENT_MINUS
            self.__updateCommentSubstate(char)
        elif self.__state == FileProcessor.MULTILINE_COMMENT_PRAGMA:
            if char == "-":
                self.__state = FileProcessor.MULTILINE_COMMENT_PRAGMA_MINUS
        elif self.__state == FileProcessor.MULTILINE_COMMENT_MINUS:
            if char == "}":
                self.__startState()
            elif char == "-":
                self.__updateCommentSubstate(char)
                pass
            else:
                self.__updateCommentSubstate(char)
                self.__state = FileProcessor.MULTILINE_COMMENT
        elif self.__state == FileProcessor.MULTILINE_COMMENT_PRAGMA_MINUS:
            if char == "}":
                self.__startState()
            elif char == "-":
                pass
            else:
                self.__state = FileProcessor.MULTILINE_COMMENT_PRAGMA
        elif self.__state == FileProcessor.STRING:
            if char == "\\":
                self.__state = FileProcessor.STRING_QUOTE
            elif char == '"':
                self.__startState()
        elif self.__state == FileProcessor.CHAR:
            if char == "\\":
                self.__state = FileProcessor.CHAR_QUOTE
            elif char == "'":
                self.__startState()
        elif self.__state == FileProcessor.STRING_MULTILINE:
            if char.isspace():
                pass
            elif char == '\\':
                self.__state = FileProcessor.STRING
            else:
                print [char]
                assert False
        elif self.__state == FileProcessor.STRING_QUOTE:
            self.__state = FileProcessor.STRING
        elif self.__state == FileProcessor.CHAR_QUOTE:
            self.__state = FileProcessor.CHAR

    def __updateStartSubstate (self, char):
        assert ( self.__state == FileProcessor.START
                or self.__state == FileProcessor.START_ALPHANUM
                )
        if self.__substate == FileProcessor.SUBSTATE_START_NEW:
            if char == 'i':
                self.__substate = FileProcessor.SUBSTATE_START_I
            else:
                self.__substate = FileProcessor.SUBSTATE_START_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_START_I:
            if char == 'm':
                self.__substate = FileProcessor.SUBSTATE_START_IM
            else:
                self.__substate = FileProcessor.SUBSTATE_START_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_START_IM:
            if char == 'p':
                self.__substate = FileProcessor.SUBSTATE_START_IMP
            else:
                self.__substate = FileProcessor.SUBSTATE_START_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_START_IMP:
            if char == 'o':
                self.__substate = FileProcessor.SUBSTATE_START_IMPO
            else:
                self.__substate = FileProcessor.SUBSTATE_START_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_START_IMPO:
            if char == 'r':
                self.__substate = FileProcessor.SUBSTATE_START_IMPOR
            else:
                self.__substate = FileProcessor.SUBSTATE_START_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_START_IMPOR:
            if char == 't':
                self.__substate = FileProcessor.SUBSTATE_START_IMPORT
            else:
                self.__substate = FileProcessor.SUBSTATE_START_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_START_IMPORT:
            if char.isspace():
                self.__substate = FileProcessor.SUBSTATE_START_IMPORT_SPACE
            else:
                self.__substate = FileProcessor.SUBSTATE_START_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_START_IMPORT_SPACE:
            pass
        elif self.__substate == FileProcessor.SUBSTATE_START_IMPORT_SPACE_NEW:
            if char == 'i':
                self.__substate = FileProcessor.SUBSTATE_START_I
            elif char.isspace():
                self.__substate = FileProcessor.SUBSTATE_START_IMPORT_SPACE
            else:
                self.__substate = FileProcessor.SUBSTATE_START_MIDDLE

    def __updateCommentSubstate (self, char):
        assert self.__state in [
            FileProcessor.SINGLE_LINE_COMMENT,
            FileProcessor.MULTILINE_COMMENT_START,
            FileProcessor.MULTILINE_COMMENT,
            FileProcessor.MULTILINE_COMMENT_MINUS]
        if self.__substate == FileProcessor.SUBSTATE_COMMENT_NEW:
            if char.isspace() or char in "<":
                pass
            elif char == "h":
                self.__substate = FileProcessor.SUBSTATE_COMMENT_H
            else:
                self.__substate = FileProcessor.SUBSTATE_COMMENT_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_COMMENT_H:
            if char == "t":
                self.__substate = FileProcessor.SUBSTATE_COMMENT_HT
            else:
                self.__substate = FileProcessor.SUBSTATE_COMMENT_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_COMMENT_HT:
            if char == "t":
                self.__substate = FileProcessor.SUBSTATE_COMMENT_HTT
            else:
                self.__substate = FileProcessor.SUBSTATE_COMMENT_MIDDLE
        elif self.__substate == FileProcessor.SUBSTATE_COMMENT_HTT:
            if char == "p":
                self.__substate = FileProcessor.SUBSTATE_COMMENT_HTTP
            else:
                self.__substate = FileProcessor.SUBSTATE_COMMENT_MIDDLE

    def __startState(self):
        self.__state = FileProcessor.START
        self.__substate = FileProcessor.SUBSTATE_START_MIDDLE

    def __startSingleLineComment(self):
        self.__state = FileProcessor.SINGLE_LINE_COMMENT
        self.__substate = FileProcessor.SUBSTATE_COMMENT_NEW

    def __startMultiLineComment(self):
        self.__state = FileProcessor.MULTILINE_COMMENT_START
        self.__substate = FileProcessor.SUBSTATE_COMMENT_NEW

    def __procesEndOfLine(self):
        if self.__state == FileProcessor.SINGLE_LINE_COMMENT:
            self.__startState()
        elif self.__state == FileProcessor.STRING_QUOTE:
            self.__state = FileProcessor.STRING_MULTILINE
        elif self.__state == FileProcessor.MULTILINE_COMMENT_START:
            self.__state == FileProcessor.MULTILINE_COMMENT
            self.__substate = FileProcessor.SUBSTATE_COMMENT_NEW
        elif self.__state == FileProcessor.MULTILINE_COMMENT:
            self.__substate = FileProcessor.SUBSTATE_COMMENT_NEW
        elif self.__state == FileProcessor.MULTILINE_COMMENT_MINUS:
            self.__state == FileProcessor.MULTILINE_COMMENT
            self.__substate = FileProcessor.SUBSTATE_COMMENT_NEW
        elif self.__state == FileProcessor.MULTILINE_COMMENT_PRAGMA:
            self.__state == FileProcessor.MULTILINE_COMMENT
            self.__substate = FileProcessor.SUBSTATE_COMMENT_NEW
        elif self.__state == FileProcessor.MULTILINE_COMMENT_PRAGMA_MINUS:
            self.__state == FileProcessor.MULTILINE_COMMENT
            self.__substate = FileProcessor.SUBSTATE_COMMENT_NEW

        if (self.__state == FileProcessor.START
                or self.__state == FileProcessor.START_ALPHANUM):
            self.__state = FileProcessor.START
            if self.__substate == FileProcessor.SUBSTATE_START_IMPORT_SPACE:
                self.__substate = FileProcessor.SUBSTATE_START_IMPORT_SPACE_NEW
            else:
                self.__substate = FileProcessor.SUBSTATE_START_NEW

    def __error80Chars(self, line_number):
        self.__name_printer.run()
        self.__error_count += 1
        print ('%s:%d: More than 80 chars.' % (self.__name, line_number))

    def finish(self):
        pass

def main(args):
    with io.open(args[0], mode = 'rt', encoding='utf-8') as f:
        processor = FileProcessor(args[0])
        line_number = 0
        for l in f.readlines():
            line_number += 1
            processor.processLine(line_number, l.rstrip('\n\r'))
        processor.finish()
        exit(processor.error_count())

if __name__ == "__main__":
    main(sys.argv[1:])