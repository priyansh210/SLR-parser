from pprint import *
import pandas as pd
from IPython.display import display, HTML


class Grammar:
    def __init__(self, grammar_str):
        self.grammar_str = grammar_str
        self.grammar = {}
        self.start = None
        self.terminals = set()
        self.nonterminals = set()

        for production in list(filter(None, grammar_str.splitlines())):
            head, _, bodies = production.partition(" -> ")

            if not head.isupper():
                print("jj", head, bodies)
                raise ValueError(
                    f"'{head} -> {bodies}': Head '{head}' is not capitalized to be treated as a nonterminal."
                )

            if not self.start:
                self.start = head

            self.grammar.setdefault(head, set())
            self.nonterminals.add(head)
            bodies = {
                tuple(body.split()) for body in " ".join(bodies.split()).split("|")
            }

            for body in bodies:
                if "^" in body and body != ("^",):
                    raise ValueError(
                        f'\'{head} -> {" ".join(body)}\': Null symbol \'^\' is not allowed here.'
                    )

                self.grammar[head].add(body)

                for symbol in body:
                    if not symbol.isupper() and symbol != "^":
                        self.terminals.add(symbol)
                    elif symbol.isupper():
                        self.nonterminals.add(symbol)

        self.symbols = self.terminals | self.nonterminals

        # debug
        # print("Grammar\n\n", self.grammar)
        # print("Start\n\n", self.start)

        # print("Terminals\n\n", self.terminals)
        # print("Non Terminals\n\n", self.nonterminals)
        # print("Grammar Str\n\n", self.grammar_str)


def first_follow(G):
    def union(set_1, set_2):
        set_1_len = len(set_1)
        set_1 |= set_2

        return set_1_len != len(set_1)

    first = {symbol: set() for symbol in G.symbols}
    first.update((terminal, {terminal}) for terminal in G.terminals)
    follow = {symbol: set() for symbol in G.nonterminals}
    follow[G.start].add("$")

    while True:
        updated = False

        for head, bodies in G.grammar.items():
            for body in bodies:
                for symbol in body:
                    if symbol != "^":
                        updated |= union(first[head], first[symbol] - set("^"))

                        if "^" not in first[symbol]:
                            break
                    else:
                        updated |= union(first[head], set("^"))
                else:
                    updated |= union(first[head], set("^"))

                aux = follow[head]
                for symbol in reversed(body):
                    if symbol == "^":
                        continue
                    if symbol in follow:
                        updated |= union(follow[symbol], aux - set("^"))
                    if "^" in first[symbol]:
                        aux = aux | first[symbol]
                    else:
                        aux = first[symbol]

        if not updated:
            return first, follow


class SLRParser:
    def __init__(self, G):
        self.G_prime = Grammar(f"{G.start}' -> {G.start}\n{G.grammar_str}")
        self.max_G_prime_len = len(max(self.G_prime.grammar, key=len))
        self.G_indexed = []

        for head, bodies in self.G_prime.grammar.items():
            for body in bodies:
                self.G_indexed.append([head, body])

        self.first, self.follow = first_follow(self.G_prime)
        self.C = self.items(self.G_prime)  # canonical collection
        self.action = list(self.G_prime.terminals) + ["$"]
        self.goto = list(self.G_prime.nonterminals - {self.G_prime.start})
        self.parse_table_symbols = self.action + self.goto
        self.parse_table = self.construct_table()

    def CLOSURE(self, I):
        J = I

        while True:
            item_len = len(J)

            for head, bodies in J.copy().items():
                for body in bodies.copy():
                    if "." in body[:-1]:
                        symbol_after_dot = body[body.index(".") + 1]

                        if symbol_after_dot in self.G_prime.nonterminals:
                            for G_body in self.G_prime.grammar[symbol_after_dot]:
                                J.setdefault(symbol_after_dot, set()).add(
                                    (".",) if G_body == ("^",) else (".",) + G_body
                                )

            if item_len == len(J):
                return J

    def GOTO(self, I, X):
        goto = {}

        for head, bodies in I.items():
            for body in bodies:
                if "." in body[:-1]:
                    dot_pos = body.index(".")

                    if body[dot_pos + 1] == X:
                        replaced_dot_body = (
                            body[:dot_pos] + (X, ".") + body[dot_pos + 2 :]
                        )

                        for C_head, C_bodies in self.CLOSURE(
                            {head: {replaced_dot_body}}
                        ).items():
                            goto.setdefault(C_head, set()).update(C_bodies)

        return goto

    def items(self, G_prime):
        C = [self.CLOSURE({G_prime.start: {(".", G_prime.start[:-1])}})]
        while True:
            item_len = len(C)

            for I in C.copy():
                for X in G_prime.symbols:
                    goto = self.GOTO(I, X)

                    if goto and goto not in C:
                        C.append(goto)

            if item_len == len(C):
                # print the canonical collection

                return C

    def construct_table(self):
        parse_table = {
            r: {c: "" for c in self.parse_table_symbols} for r in range(len(self.C))
        }

        for i, I in enumerate(self.C):
            for head, bodies in I.items():
                for body in bodies:
                    if "." in body[:-1]:  # CASE 2 a
                        symbol_after_dot = body[body.index(".") + 1]

                        if symbol_after_dot in self.G_prime.terminals:
                            s = f"s{self.C.index(self.GOTO(I, symbol_after_dot))}"

                            if s not in parse_table[i][symbol_after_dot]:
                                if "r" in parse_table[i][symbol_after_dot]:
                                    parse_table[i][symbol_after_dot] += "/"

                                parse_table[i][symbol_after_dot] += s

                    elif body[-1] == "." and head != self.G_prime.start:  # CASE 2 b
                        for j, (G_head, G_body) in enumerate(self.G_indexed):
                            if G_head == head and (
                                G_body == body[:-1]
                                or G_body == ("^",)
                                and body == (".",)
                            ):
                                for f in self.follow[head]:
                                    if parse_table[i][f]:
                                        parse_table[i][f] += "/"

                                    parse_table[i][f] += f"r{j}"

                                break

                    else:  # CASE 2 c
                        parse_table[i]["$"] = "acc"

            for A in self.G_prime.nonterminals:  # CASE 3
                j = self.GOTO(I, A)

                if j in self.C:
                    parse_table[i][A] = self.C.index(j)

        return parse_table

    def print_info(self):
        def fprint(text, variable):
            print(f'{text:>12}: {", ".join(variable)}')

        print("AUGMENTED GRAMMAR:")

        for i, (head, body) in enumerate(self.G_indexed):
            print(f'{str(i)}: {head} -> {" ".join(body)}')

        print()
        print("CANONICAL COLLECTION of LR(0) ITEMS:")
        for i, productions in enumerate(self.C):
            print("----I" + str(i) + "----")
            for P in productions:
                for NT in productions[P]:
                    print(P, "->", " ".join(NT))

            print()

        fprint("TERMINALS", self.G_prime.terminals)
        fprint("NONTERMINALS", self.G_prime.nonterminals)
        fprint("SYMBOLS", self.G_prime.symbols)

        print("\nFIRST:")
        for head in self.G_prime.grammar:
            print(f'{head} = {{ {", ".join(self.first[head])} }}')

        print("\nFOLLOW:")
        for head in self.G_prime.grammar:
            print(f'{head} = {{ {", ".join(self.follow[head])} }}')

        headers = ["ACTION"] * (1 + len(self.G_prime.terminals)) + ["GOTO"] * (
            len(self.G_prime.nonterminals) - 1
        )

        print("\nPARSING TABLE:")
        print()
        PARSE_TABLE = pd.DataFrame(self.parse_table).T
        PARSE_TABLE.columns = [headers, list(PARSE_TABLE.columns)]
        print(PARSE_TABLE)

    def LR_parser(self, w):
        buffer = f"{w} $".split()
        pointer = 0
        a = buffer[pointer]
        stack = ["0"]
        symbols = [""]
        results = {
            "step": [],
            "stack": [] + stack,
            "symbols": [] + symbols,
            "input": [],
            "action": [],
        }

        step = 0
        while True:
            s = int(stack[-1])
            step += 1
            results["step"].append(f"({step})")
            results["input"].append(" ".join(buffer[pointer:]))

            if a not in self.parse_table[s]:
                results["action"].append(f"ERROR: unrecognized symbol {a}")

                break

            elif not self.parse_table[s][a]:
                results["action"].append(
                    "ERROR: input cannot be parsed by given grammar"
                )

                break

            elif "/" in self.parse_table[s][a]:
                action = "reduce" if self.parse_table[s][a].count("r") > 1 else "shift"
                results["action"].append(
                    f"ERROR: {action}-reduce conflict at state {s}, symbol {a}"
                )

                break

            elif self.parse_table[s][a].startswith("s"):
                results["action"].append("shift")
                stack.append(self.parse_table[s][a][1:])
                symbols.append(a)
                results["stack"].append(" ".join(stack))
                results["symbols"].append(" ".join(symbols))
                pointer += 1
                a = buffer[pointer]

            elif self.parse_table[s][a].startswith("r"):
                head, body = self.G_indexed[int(self.parse_table[s][a][1:])]
                results["action"].append(f'reduce by {head} -> {" ".join(body)}')

                if body != ("^",):
                    stack = stack[: -len(body)]
                    symbols = symbols[: -len(body)]

                stack.append(str(self.parse_table[int(stack[-1])][head]))
                symbols.append(head)
                results["stack"].append(" ".join(stack))
                results["symbols"].append(" ".join(symbols))

            elif self.parse_table[s][a] == "acc":
                results["action"].append("accept")

                break

        return results

    def print_LR_parser(self, results):
        df = pd.DataFrame(results)
        df.style.set_table_styles(
            [{"selector": "", "props": [("border", "10px solid yellow")]}]
        )
        print("\n")
        print(df)


filename = "testGrammar.txt"

# Read the file and concatenate it
with open(filename, "r") as f:
    file_contents = f.readlines()
    grammar_str = "".join(filter(None, file_contents))

# create a Grammar object
G = Grammar(grammar_str)

slr_parser = SLRParser(G)
slr_parser.print_info()

TOKEN = "id + id + id * id"

results = slr_parser.LR_parser(TOKEN)
slr_parser.print_LR_parser(results)
