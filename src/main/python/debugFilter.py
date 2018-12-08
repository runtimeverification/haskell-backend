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
    chunks = []
    while True:
        (start, end) = findElementStartingWith(0, ", idLocation =", line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
        chunks.append(line[:start])
        line = line[end:]

def cleanApplication(line):
    """Removes the redundant parts of ApplicationPattern patterns.

    The result will look something like
    "symbol"[arg1, arg2, ...](phi1, phi2, ....)
    """
    chunks = []
    while True:
        (start, end) = findElementStartingWith(
            0,
            "Fix (ApplicationPattern",
            line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
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
        chunks.append(line[:start])
        chunks.append(line[symbolStart : symbolEnd])
        chunks.append("(")
        chunks.append(
            cleanApplication(line[childrenStart + 1: childrenEnd - 1]))
        chunks.append(")")
        line = line[end : ]

def cleanSort(line):
    """Removes the redundant parts of SortActual sorts.

    The result will look something like
    "sort-name"{sort1, sort2, ...}
    """
    chunks = []
    while True:
        (start, end) = findElementStartingWith(
            0,
            "SortActualSort (SortActual",
            line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
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
        chunks.append(line[:start])
        chunks.append(line[symbolStart : symbolEnd])
        chunks.append(cleanSort(line[childrenStart : childrenEnd]))
        line = line[end : ]

def cleanVariable(line):
    """Removes the redundant parts of Variables.

    The result will look something like
    "variable-name":sort
    """
    chunks = []
    while True:
        (start, end) = findElementStartingWith(
            0,
            "Variable {variableName",
            line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
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
        chunks.append(line[:start])
        chunks.append(line[symbolStart : symbolEnd])
        chunks.append(":")
        chunks.append(line[sortStart : sortEnd])
        line = line[end : ]

def cleanBottom(line):
    """Rewrites bottom patterns."""
    chunks = []
    while True:
        (start, end) = findElementStartingWith(0, "Fix (BottomPattern", line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
        chunks.append(line[:start])
        chunks.append("⊥")
        line = line[end:]

def cleanTop(line):
    """Rewrites top patterns."""
    chunks = []
    while True:
        (start, end) = findElementStartingWith(0, "Fix (TopPattern", line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
        chunks.append(line[:start])
        chunks.append("T")
        line = line[end:]

def cleanStepProof(line):
    """Removes StepProofs"""
    chunks = []
    while True:
        (start, end) = findElementStartingWith(0, "StepProof {", line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
        chunks.append(line[:start])
        chunks.append(" proof")
        line = line[end:]

def cleanStringDomainValue(line):
    """Cleans string domain values"""
    chunks = []
    while True:
        (start, end) = findElementStartingWith(
            0,
            "Fix (DomainValuePattern (DomainValue",
            line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
        (sortStart, sortEnd) = findElementAndSkipPrefix(
            start,
            "domainValueSort = ",
            line)
        assert sortStart > 0
        (childStart, childEnd) = findElementAndSkipPrefix(
            start,
            "domainValueChild = ",
            line)
        assert childStart > 0
        assert childEnd < end
        isString = line[childStart:].startswith(
            "BuiltinPattern (Fix (StringLiteral")
        if not isString:
            chunks.append(line[start])
            line = line[start + 1:]
            continue
        (valueStart, valueEnd) = findElementAndSkipPrefix(
            start,
            "getStringLiteral = ",
            line)
        assert valueStart > 0
        assert valueEnd <= end
        chunks.append(line[:start])
        chunks.append("DomainValue(")
        chunks.append(line[valueStart : valueEnd])
        chunks.append(":")
        chunks.append(line [sortStart : sortEnd])
        chunks.append(")")
        line = line[end:]

def cleanStandardPattern(name, line):
    """Simplifies the (Fix (<name>Pattern(<name>))) part of patterns"""
    prefix = "Fix (" + name + "Pattern (" + name
    chunks = []
    while True:
        (start, end) = findElementStartingWith(0, prefix, line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
        chunks.append(line[:start])
        chunks.append(name)
        chunks.append(
            cleanStandardPattern(name, line[start + len(prefix) : end - 2]))
        line = line[end:]

def cleanVariablePattern(line):
    """Simplifies the (Fix (VariablePattern(...))) part of patterns"""
    prefix = "Fix (VariablePattern ("
    chunks = []
    while True:
        (start, end) = findElementStartingWith(0, prefix, line)
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
        chunks.append(line[:start])
        chunks.append("Variable (")
        chunks.append(line[start + len(prefix) : end - 1])
        line = line[end:]

def unescapeSequence(sequence):
    return (sequence[1:len(sequence) - 1]
        .replace("Unds", "_")
        .replace("Plus", "+")
        .replace("Slsh", "/")
        .replace("Star", "*")
        .replace("-LT-", "<")
        .replace("-GT-", ">")
        .replace("Eqls", "=")
        .replace("Pipe", "|")
        .replace("Hash", "#")
        .replace("LPar", "(")
        .replace("RPar", ")")
        .replace("LBra", "{")
        .replace("RBra", "}")
        .replace("Ques", ".")
        .replace("Stop", ".")
        .replace("Comm", ",")
        .replace("SCln", ";")
    )

def unescapeIdentifier(identifier):
    nextStart = 0
    while True:
        start = identifier.find("'", nextStart)
        if start < 0:
            return identifier
        end = identifier.find("'", start + 1)
        assert end > 0
        changed = unescapeSequence(identifier[start:end + 1])
        identifier = identifier[:start] + changed + identifier[end + 1:]
        nextStart = start + len(changed)

def cleanIdentifierEscaping(line):
    """Simplifies things like Lbl'UndsPlus'Int'Unds' to _+Int_"""
    chunks = []
    while True:
        start = line.find('"Lbl')
        if start < 0:
            chunks.append(line)
            return "".join(chunks)
        end = line.find('"', start + 1)
        assert end > 0
        changed = unescapeIdentifier(line[start:end + 1])
        chunks.append(line[:start])
        chunks.append(changed)
        line = line[end + 1:]

def cleanStandardPatterns(line):
    return cleanStandardPattern("And",
        cleanStandardPattern("Ceil",
        cleanStandardPattern("DomainValue",
        cleanStandardPattern("Equals",
        cleanStandardPattern("Exists",
        cleanStandardPattern("Floor",
        cleanStandardPattern("Forall",
        cleanStandardPattern("Iff",
        cleanStandardPattern("Implies",
        cleanStandardPattern("In",
        cleanStandardPattern("Next",
        cleanStandardPattern("Not",
        cleanStandardPattern("Or",
        cleanStandardPattern("Rewrites",
        cleanVariablePattern(line)))))))))))))))

def clean(line):
    """Applies known cleaning algorithms to the line."""
    return cleanBottom(cleanTop(cleanStepProof(cleanIdentifierEscaping(
        cleanStandardPatterns(cleanStringDomainValue(
        cleanVariable(cleanSort(cleanApplication(cleanIdLocation(line))))))))))

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
