#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Filters the stdin input to make kore debugging output readable. It was created
to handle output produced by the Kore.Debug Haskell package, but may improve
any kore pattern displayed with 'show'.

Example usage:
cat debug.txt | ./debugFilter.py

It is especially useful when used with 'debugger.py'
"""
import cProfile
import re
import sys

class Structure:
    """Tree-like representation for debug output lines.

    A node has a title and some children.

    It uses (,) as delimiters.
    """
    def __init__(self, txt, children):
        self.__text = txt
        self.__children = children

    def __str__(self):
        return "".join(self._chunks([]))

    def _chunks(self, chunks):
        chunks.append(self.__text)
        if not self.__children:
            return
        chunks.append("(")
        first = True
        for p in self.__children:
            if first:
                first = False
            else:
                chunks.append(",")
            p._chunks(chunks)
        chunks.append(")")
        return chunks

    def size(self):
        """Child count."""
        return len(self.__children)

    def child(self, index):
        """Returns the child with the given index."""
        return self.__children[index]

    def text(self):
        """Returns the title node."""
        return self.__text

    def children(self):
        """Returns the children collection."""
        return self.__children

    def replaceWith(self, node):
        """Replaces the self contents with the given node."""
        self.__text = node.__text
        self.__children = node.__children

    def removeSubnode(self, path):
        """Removes the subnode identified by path.

        The path elements should match a chain of descendant titles,
        starting with a child of the current node. Returns the last descendant
        in the chain.

        Matching means that the path element occurs as a substring in the title.
        """
        assert path
        node = self
        pindex = 0
        while True:
            for index in xrange(0, len(node.__children)):
                child = node.__children[index]
                if child.text().find(path[pindex]) >= 0:
                    if pindex == len(path) - 1:
                        del self.__children[index]
                        return
                    node = child
                    pindex += 1
                    break
            assert False

    def getSubnode(self, path):
        """Finds the subnode identified by path.

        The path elements should match a chain of descendant titles,
        starting with a child of the current node. Returns the last descendant
        in the chain.

        Matching means that the path element occurs as a substring in the title.
        """
        assert path
        node = self
        pindex = 0
        while pindex < len(path):
            found = False
            for index in xrange(0, len(node.__children)):
                child = node.__children[index]
                if child.text().find(path[pindex]) >= 0:
                    node = child
                    pindex += 1
                    found = True
                    break
            assert found, str(pindex) + " " + str(path) + " " + str(node)
        return node

    def hasChild(self, name):
        """Whether the current node has a child with the given title.

        Matching means that the path element occurs as a substring in the title.
        """
        for child in self.__children:
            if child.text().find(name) >= 0:
                return True
        return False

class Line:
    """The root node of a debug tree.

    Also handles parsing and serialization.
    """
    __open_re = re.compile(r"\(|\[|\{")
    __close_re = re.compile(r"\)|\]|\}")
    __comma_re = re.compile(r",")

    def __init__(self, line):
        lineChunks = [c for c in Line.__split(line) if c]
        self.__parsed = []
        index = 0
        while index < len(lineChunks):
            (newIndex, parsed) = Line.__parse(lineChunks, index)
            self.__parsed.append(parsed)
            assert index < newIndex
            index = newIndex

    @staticmethod
    def __split(line):
        return Line.__splitWithRe(Line.__open_re, "(",
            Line.__splitWithRe(Line.__close_re, ")",
                Line.__splitWithRe(Line.__comma_re, ",", [line])))

    @staticmethod
    def __splitWithRe(regexp, joiner, chunks):
        def split():
            for c in chunks:
                first = True
                for s in regexp.split(c):
                    if not first:
                        yield joiner
                    else:
                        first = False
                    yield s
        return list(split())

    @staticmethod
    def __parse(chunks, index):
        if chunks[index] == "(":
            title = ""
        else:
            title = chunks[index]
            index += 1
        if index == len(chunks):
            return (index, Structure(title, []))
        children = []
        if chunks[index] == "(":
            index += 1
            if index == len(chunks):
                return (index, Structure(title, []))

            if chunks[index] == ")":
                children.append(Structure("", []))
                index = index + 1
            else:
                while chunks[index] != ")":
                    (index, child) = Line.__parse(chunks, index)
                    children.append(child)
                    if index >= len(chunks):
                        break
                    if chunks[index] == ",":
                        index += 1
                if index < len(chunks):
                    assert chunks[index] == ")"
                    index = index + 1
        return (index, Structure(title, children))

    def __str__(self):
        return "".join(self._chunks([]))

    def _chunks(self, chunks):
        first = True
        for p in self.__parsed:
            if first:
                first = False
            else:
                chunks.append(",")
            p._chunks(chunks)
        return chunks

    def find(self, path, iterator):
        """Finds a node matched by the given path.

        A node matches a path if the node matches the first element of the
        path, with a chain of descendants matching the reminder of the path.

        A node matches a path element if its title is equal to the element.
        As exceptions, the first node matches if the path element is a suffix,
        the last node matches if the path element is a prefix.
        """
        if iterator is None:
            iterator = Iterator(self)
        element = iterator.element()
        while iterator.isValid():
            if self.__match(element, path, 0):
                return True
            element = iterator.next()
        return False

    def __match(self, element, path, index):
        if index >= len(path):
            return True

        if index == 0:
            if not element.text().endswith(path[index]):
                return False
        elif index == len(path) - 1:
            if not element.text().startswith(path[index]):
                return False
        else:
            if not element.text() == path[index]:
                return False

        for i in xrange(0, element.size()):
            if self.__match(element.child(i), path, index + 1):
                return True
        return False

    def size(self):
        """Returns the number of children."""
        return len(self.__parsed)

    def child(self, index):
        """Returns the child with the given index."""
        return self.__parsed[index]

    def text(self):
        """Default implementation to match the same interface as 'Structure'."""
        return ""

def printLine (indentLevel, line):
    """Displays a text using the given indentation."""
    print("    " * indentLevel + str(line))

class IteratorElement:
    """Helper for iterating over a debug tree.

    Stops first at the root, then at each child.
    """
    def __init__(self, structure):
        self.__structure = structure
        self.__index = 0
        self.__child = None
        self.__isValid = True

    def next(self):
        """Advances the iterator to the next child.

        Returns the child, or 'None' if the iteration ended.
        """
        self.__isValid = False
        if self.__index >= self.__structure.size():
            return None
        self.__child = self.__structure.child(self.__index)
        self.__index += 1
        return self.__child

    def element(self):
        """Returns the iterator's main node."""
        if not self.__isValid:
            return None
        return self.__structure


class Iterator:
    """Iterates over a debug tree.

    Also stops at intermediate nodes, not only at leaves.
    """
    def __init__(self, structure):
        self.__elements = [IteratorElement(structure)]

    def next(self):
        """Advances the iterator.

        Returns the newly reached node, or 'None' if the iteration ended.
        """
        while self.__elements:
            retv = self.__elements[-1].next()
            if retv:
                self.__elements.append(IteratorElement(retv))
                return retv
            del self.__elements[-1]
        if not self.__elements:
            return None

    def element(self):
        """Returns the current node."""
        if not self.__elements:
            return None
        return self.__elements[-1].element()

    def isValid(self):
        """Whether the iteration ended."""
        return len(self.__elements) > 0

    def __str__(self):
        elements = [str(e) for e in self.__elements]
        return "idx[" + ",".join(elements) + "]"


def cleanIdLocation(line):
    """Removes the idLocation part of Id structs."""
    iterator = Iterator(line)
    while True:
        if not line.find(["Id ", " idLocation = AstLocationFile "], iterator):
            return line
        iterator.element().removeSubnode(["idLocation"])

def cleanApplication(line):
    """Removes the redundant parts of ApplicationPattern patterns.

    The result will look something like
    "symbol"[arg1, arg2, ...](phi1, phi2, ....)
    """
    it = Iterator(line)
    while line.find(["CofreeT ", "Identity ", " :< ApplicationPattern"], it):
        app = it.element().getSubnode(
            ["Identity ", "ApplicationPattern", "Application"])
        symbol = app.getSubnode(["applicationSymbolOrAlias"])
        children = app.getSubnode(["applicationChildren"])
        name = symbol.getSubnode(["symbolOrAliasConstructor", "getId"])
        sorts = symbol.getSubnode(["symbolOrAliasParams"])
        nameText = name.text()[8:]
        if sorts.size():
            result = Structure(
                nameText,
                [ Structure("", sorts.children())
                , Structure("", children.children())
                ]
            )
        else:
            result = Structure(
                nameText,
                children.children()
            )
        it.element().replaceWith(result)
    return line

def cleanSort(line):
    """Removes the redundant parts of SortActual sorts.

    The result will look something like
    "sort-name"{sort1, sort2, ...}
    """
    it = Iterator(line)
    while line.find(["SortActualSort ", "SortActual"], it):
        sort = it.element().getSubnode(["SortActual"])
        sorts = sort.getSubnode(["sortActualSorts"])
        name = sort.getSubnode(["sortActualName", "getId"])

        nameText = name.text()[8:]
        result = Structure(
            nameText,
            sorts.children()
        )
        it.element().replaceWith(result)
    return line

def cleanVariable(line):
    """Removes the redundant parts of Variables.

    The result will look something like
    "variable-name":sort
    """
    it = Iterator(line)
    while line.find(["Variable ", "variableName"], it):
        sort = it.element().getSubnode(["variableSort"])
        name = it.element().getSubnode(["variableName", "getId"])

        nameText = name.text()[8:]
        result = Structure(
            nameText + ":",
            [sort]
        )
        it.element().replaceWith(result)
    return line

def cleanStringDomainValue(line):
    """Cleans string domain values"""
    it = Iterator(line)
    while line.find(
            ["CofreeT ", "Identity ", " :< DomainValuePattern ",
                "DomainValue ", " domainValueChild = BuiltinPattern ",
                "PurePattern ", "getPurePattern = CofreeT ", "Identity ",
                " :< StringLiteralPattern "], it):
        dv = it.element().getSubnode(
            ["Identity ", " :< DomainValuePattern ", "DomainValue "]
        )
        sort = dv.getSubnode(["domainValueSort"])
        value = dv.getSubnode(
            ["domainValueChild", "PurePattern", "getPurePattern",
                "Identity", "StringLiteralPattern", "StringLiteral",
                "getStringLiteral"
            ]
        )

        valueText = value.text()[len("getStringLiteral = "):]
        result = Structure(
            valueText + ":",
            [sort]
        )
        it.element().replaceWith(result)
    return line

def cleanStepProof(line):
    """Removes StepProofs"""
    it = Iterator(line)
    while line.find(["StepProof "], it):
        it.element().replaceWith(Structure("proof", []))
    return line

def cleanBottom(line):
    """Rewrites bottom patterns."""
    it = Iterator(line)
    while line.find(["CofreeT ", "Identity ", " :< BottomPattern "], it):
        it.element().replaceWith(Structure("⊥", []))
    return line

def cleanTop(line):
    """Rewrites top patterns."""
    it = Iterator(line)
    while line.find(["CofreeT ", "Identity ", " :< TopPattern "], it):
        it.element().replaceWith(Structure("T", []))
    return line

def cleanStandardPattern(name, line):
    """Simplifies the redundant part of patterns"""
    patternName = " :< " + name + "Pattern "

    it = Iterator(line)
    while line.find(["CofreeT ", "Identity ", patternName, name], it):
        node = it.element().getSubnode(["Identity ", patternName, name])
        it.element().replaceWith(node)
    return line

def cleanVariablePattern(line):
    """Simplifies the Cofree part of variables."""
    it = Iterator(line)
    while line.find(["CofreeT ", "Identity ", " :< VariablePattern "], it):
        node = it.element().getSubnode(["Identity ", " :< VariablePattern "])
        it.element().replaceWith(Structure("Variable ", [node.child(0)]))
    return line

def unescapeSequence(sequence):
    """ Unescapes strings into their original representation.

    Assumes that unescaping can be freely applied on the entire string.
    """
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
    """Unescapes a K identifier from its Kore representation."""
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
    it = Iterator(line)
    while it.isValid():
        txt = it.element().text()
        start = txt.find('"Lbl')
        if start >= 0:
            chunks = []
            prevStart = 0
            while start >= 0:
                chunks.append(txt[:start])
                end = txt.find('"', start + 1)
                assert end > 0
                chunks.append(unescapeIdentifier(txt[start:end + 1]))
                prevStart = end + 1
                start = txt.find('"Lbl', prevStart)
            chunks.append(txt[prevStart:])
            it.element().replaceWith(
                Structure("".join(chunks), it.element().children()))
        it.next()
    return line

def cleanStandardPatterns(line):
    """Simpler representation for all patterns without special handling.
    """
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
    return (
        cleanIdentifierEscaping( # 28 s
            cleanBottom(
                cleanTop(  # 31 s
                    cleanStandardPatterns(  # 29 s
                        cleanSort(  # 40 sec
                            cleanVariable(  # 44 sec
                                cleanStringDomainValue( # 53 sec
                                    cleanApplication(  # 34 sec
                                        cleanIdLocation(  # 27 sec
                                            cleanStepProof( # 24 s (from 53)
                                                line  # 17 sec
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    )

def main(argv):
    sys.setrecursionlimit(4000)
    for line in sys.stdin:
        print clean(Line(line[:len(line) - 1]))

if __name__ == "__main__":
    #cProfile.run('main(sys.argv[1:])')
    main(sys.argv[1:])