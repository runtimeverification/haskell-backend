#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Filters the stdin input to make kore debugging output readable. It was created
to handle output produced by the Kore.Debug Haskell package, but may improve
any kore pattern displayed with 'show'.

Example usage:
cat debug.txt | ./debugFilter.py
"""
import sys

def printLine (indentLevel, line):
    """Displays a text using the given indentation."""
    print("    " * indentLevel + line)

def findElementEnd(start, line):
    """Finds an element's end given its start.

    Assumes a correctly parenthesized expression, with elements separated
    by commas.
    """
    end = start
    openBraces = 0
    while end < len(line) and openBraces >= 0:
        if line[end] in "({[":
            openBraces += 1
        elif line[end] in ")}]":
            if openBraces == 0:
                return end
            openBraces -= 1
            if openBraces == 0:
                return end + 1
        elif line[end] == ",":
            if openBraces == 0:
                return end
        end+= 1
    return end

def findElementStartingWith(startIndex, prefix, line):
    """Finds an element's position given a prefix and a start index.

    Assumes a correctly parenthesized expression, with elements separated
    by commas. Assumes that an expression with parenthesis ends at the last
    closed one.

    The prefix may include the preceding comma.

    Returns (-1, -1) if no such element was found.
    """
    start = line.find(prefix, startIndex)
    if start < 0:
        return (-1, -1)
    end = findElementEnd(start + 1, line)
    assert end > start
    return (start, end)

def findElementAndSkipPrefix(startIndex, prefix, line):
    """Finds an element's position given a prefix and a start index.

    Assumes a correctly parenthesized expression, with elements separated
    by commas.

    The prefix may include the preceding comma.

    Returns (-1, -1) if no such element was found. The return poosition does
    not include the prefix.
    """
    (start, end) = findElementStartingWith(startIndex, prefix, line)
    if start < 0:
        return (-1, -1)
    return (start + len(prefix), end)

def cleanIdLocation(line):
    """Removes the idLocation part of Id structs."""
    while True:
        (start, end) = findElementStartingWith(0, ", idLocation =", line)
        if start < 0:
            return line
        line = line[:start] + line[end:]

def cleanApplication(line):
    """Removes the redundant parts of ApplicationPattern patterns.

    The result will look something like
    "symbol"[arg1, arg2, ...](phi1, phi2, ....)
    """
    start = 0
    while True:
        (start, end) = findElementStartingWith(
            start,
            "Fix (ApplicationPattern",
            line)
        if start < 0:
            return line
        (childrenStart, childrenEnd) = findElementAndSkipPrefix(
            start,
            " applicationChildren = ",
            line)
        assert childrenStart > 0
        (symbolStart, symbolEnd) = findElementAndSkipPrefix(
            start,
            "getId = ",
            line)
        assert symbolStart > 0
        (symbolParamsStart, symbolParamsEnd) = findElementAndSkipPrefix(
            start,
            " symbolOrAliasParams = ",
            line)
        assert symbolParamsStart > 0
        children = line[childrenStart + 1: childrenEnd - 1]
        children = "(" + children + ")"
        line = (
            line[:start]
            + line[symbolStart : symbolEnd]
            + line[symbolParamsStart : symbolParamsEnd]
            + children
            + line[end : ]
            )

def cleanSort(line):
    """Removes the redundant parts of SortActual sorts.

    The result will look something like
    "sort-name"{sort1, sort2, ...}
    """
    start = 0
    while True:
        (start, end) = findElementStartingWith(
            start,
            "SortActualSort (SortActual",
            line)
        if start < 0:
            return line
        (childrenStart, childrenEnd) = findElementAndSkipPrefix(
            start,
            " sortActualSorts = ",
            line)
        assert childrenStart > 0
        (symbolStart, symbolEnd) = findElementAndSkipPrefix(
            start,
            "getId = ",
            line)
        assert symbolStart > 0
        line = (
            line[:start]
            + line[symbolStart : symbolEnd]
            + line[childrenStart : childrenEnd]
            + line[end : ]
            )

def cleanVariable(line):
    """Removes the redundant parts of Variables.

    The result will look something like
    "variable-name":sort
    """
    start = 0
    while True:
        (start, end) = findElementStartingWith(
            start,
            "Variable {variableName",
            line)
        if start < 0:
            return line
        (sortStart, sortEnd) = findElementAndSkipPrefix(
            start,
            " variableSort = ",
            line)
        assert sortStart > 0
        (symbolStart, symbolEnd) = findElementAndSkipPrefix(
            start,
            "getId = ",
            line)
        assert symbolStart > 0
        line = (
            line[:start]
            + line[symbolStart : symbolEnd]
            + ":"
            + line[sortStart : sortEnd]
            + line[end : ]
            )

def cleanBottom(line):
    """Rewrites bottom patterns."""
    while True:
        (start, end) = findElementStartingWith(0, "Fix (BottomPattern", line)
        if start < 0:
            return line
        line = line[:start] + "⊥" + line[end:]

def cleanTop(line):
    """Rewrites top patterns."""
    while True:
        (start, end) = findElementStartingWith(0, "Fix (TopPattern", line)
        if start < 0:
            return line
        line = line[:start] + "T" + line[end:]

def cleanStepProof(line):
    """Removes StepProofs"""
    while True:
        (start, end) = findElementStartingWith(0, "StepProof {", line)
        if start < 0:
            return line
        line = line[:start] + " proof" + line[end:]

def clean(line):
    """Applies known cleaning algorithms to the line."""
    return cleanBottom(cleanTop(cleanStepProof(
        cleanVariable(cleanSort(cleanApplication(cleanIdLocation(line)))))))

def printParseLine(indentLevel, maxOpenParenthesis, line):
    """Rudimentary attempts to split a line and indent it."""
    index = 0
    openParenthesis = 0
    lastPrinted = 0
    while index < len(line):
        if line[index] == "(":
            if openParenthesis < maxOpenParenthesis:
                printLine(indentLevel, line[lastPrinted:index + 1])
                lastPrinted = index + 1
                indentLevel += 2
            openParenthesis += 1
        elif line[index] == ")":
            if openParenthesis <= maxOpenParenthesis:
                if lastPrinted < index:
                    printLine(indentLevel, line[lastPrinted:index])
                lastPrinted = index + 1
                indentLevel -= 2
                printLine(indentLevel, ")")
            openParenthesis -= 1
        elif line[index] == ",":
            if openParenthesis <= maxOpenParenthesis:
                printLine(indentLevel, line[lastPrinted:index + 1])
                lastPrinted = index + 1
        index += 1
    if lastPrinted < len(line):
        printLine(indentLevel, line[lastPrinted:])

def printArgumentLine(indentLevel, line):
    printParseLine(indentLevel, 1, line)

def parseAndDisplay(line, indentLevel):
    """Indents lines."""
    if line.startswith("starting "):
        printArgumentLine(indentLevel, line)
        indentLevel += 1
    elif line.startswith("ending "):
        indentLevel -= 1
        printArgumentLine(indentLevel, line)
    else:
        printLine(indentLevel, line)
    return indentLevel

indentLevel = 0

for line in sys.stdin:
    indentLevel = parseAndDisplay(
        clean(line[:len(line) - 1]),
        indentLevel)
