import re
from typing import Any

class ParserException(Exception):
    pass

class Parser:
    def __init__(self, i: str):
        self.input = i

    def match(self, v: str):
        if self.input.startswith(v):
            self.input = self.input.removeprefix(v)
        else:
            raise ParserException(f"match: {self.input}")

    def is_match(self, v: str) -> bool:
        if self.input.startswith(v):
            self.input = self.input.removeprefix(v)
            return True
        else:
            return False

    def regex(self, pattern: str) -> str:
        m = re.match(r"^(" + pattern + r")(.*)$", self.input, re.DOTALL)
        if m:
            self.input = m.group(2)
            return m.group(1)
        else:
            raise ParserException(f"regex: {pattern} {self.input}")

    def ident(self) -> str:
        return self.regex(r"[a-z]+")

    def whitespace(self):
        self.regex(r"\s*")

    def string(self):
        self.match("\"")
        s = self.regex(r"(?:\\.|[^\"])*")
        self.match("\"")
        return s.encode('utf-8').decode('unicode_escape')

    def number(self) -> int:
        return int(self.regex(r"[0-9]+"))

    def bool(self) -> int:
        return bool(self.regex(r"(?:TRUE|FALSE)"))

    def collection(self):
        c = {}
        self.match("(")
        while True:
            self.whitespace()
            k = self.value()
            self.whitespace()
            self.match(":>")
            self.whitespace()
            v = self.value()
            self.whitespace()

            c[k] = v
            if self.is_match(")"):
                break

            self.match("@@")
        return c

    def tuple(self):
        t = []
        self.match("<<")
        while True:
            self.whitespace()
            v = self.value()
            self.whitespace()

            t.append(v)

            if self.is_match(">>"):
                break

            self.match(",")

        return tuple(t)

    def choose(self, items: list[str]):
        backup = self.input
        for i in items:
            try:
                f = getattr(self, i)
                r = f()
                return r
            except ParserException:
                self.input = backup

        raise ParserException(f"choose: {items} {self.input}")

    def value(self) -> Any:
        return self.choose(["number", "string", "collection", "bool", "tuple"])

    def multi_or(self) -> dict[str, Any]:
        r = {}

        self.whitespace()
        self.is_match("/\\")

        while True:
            self.whitespace()
            key = self.ident()
            self.whitespace()
            self.match("=")
            self.whitespace()
            value = self.value()

            r[key] = value

            self.whitespace()
            if not self.is_match("/\\"):
                break

        return r

    def parse(self) -> dict:
        return self.multi_or()


def test():
    i = "/\\ i = 123"
    Parser(i).parse()

    i = "/\\ a = FALSE  /\\ b = TRUE"
    Parser(i).parse()

    i = "/\\ t = <<0, 2>>"
    Parser(i).parse()

    i = "/\\ result = \"?\"\n/\\ board = ( <<0, 0>> :> \" \" @@\n  <<0, 1>> :> \" \" @@\n  <<0, 2>> :> \" \" @@\n  <<1, 0>> :> \"X\" @@\n  <<1, 1>> :> \" \" @@\n  <<1, 2>> :> \" \" @@\n  <<2, 0>> :> \" \" @@\n  <<2, 1>> :> \" \" @@\n  <<2, 2>> :> \" \" )\n/\\ turn = \"O\""
    Parser(i).parse()

    i = "node = \"A1\""
    Parser(i).parse()



#test()