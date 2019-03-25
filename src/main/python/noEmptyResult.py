#!/usr/bin/env python
# -*- coding: utf-8 -*-
import curses
import sys
import time

class Debug:
    def __init__(self, text):
        self.__objects = []
        self.__text = text

    def add(self, object):
        self.__objects.append(object)

    def write(self):
        print self.__text
        for o in self.__objects:
            o.write()

def parseLine(line):
    parsed = Debug(line)
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
            if line.startswith("ending D_Step with result:"):
                line = "ending D_Step with result: (*)"
        except StopIteration:
            break
        line = line.replace("((),", "(")
        line = line.replace("((),", "(")
        line = line.replace("((),", "(")
        line = line.replace("((),", "(")
        line = line.replace("((),", "(")
        line = line.replace(",())", ")")
        line = line.replace(",())", ")")
        line = line.replace(",())", ")")
        line = line.replace(",())", ")")
        line = line.replace(",())", ")")
        line = line.replace(",(),", ",")
        line = line.replace(",(),", ",")
        line = line.replace(",(),", ",")
        line = line.replace(",(),", ",")
        line = line.replace(",(),", ",")
        line = line.replace(",(),", ",")
        line = line.replace(",(),", ",")
        line = line.replace("),()", ")")
        line = line.replace("()", "")
        line = line.replace("()", "")
        line = line.replace("()", "")
        line_debug = parseLine(line)
        if startsLevel(line):
            childLine = readDebug(line_debug, it, indent_level + 1)
            if not (childLine is None):
                debug.add(childLine)
            continue
        debug.add(line_debug)
        if endsLevel(line):
            dropThing = line.endswith("result: ")
            break
    if dropThing:
        return None
    return debug

def main(args):
    sys.setrecursionlimit(5000)
    with open(args[0]) as f:
        debug = readDebug(
            Debug(0),
            iter([l[ : len(l) - 1] for l in f.readlines()]),
            0)
        debug.write()


if __name__ == "__main__":
    main(sys.argv[1:])
