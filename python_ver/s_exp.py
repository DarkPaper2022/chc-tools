
# Being explicit about Types
Symbol = str
Number = (int, float)
Atom = (Symbol, Number)
List = list
Expr = (Atom, List)



def tokenize(chars: str) -> list:
    """Convert a string of characters into a list of tokens."""
    return chars.replace('(', ' ( ').replace(')', ' ) ').replace('" "', 'space').split()


def parse_sexpression(program: str) -> Expr:
    """Read an S-expression from a string."""
    return read_from_tokens(tokenize(program))


def read_from_tokens(tokens: list) -> Expr:
    """Read an expression from a sequence of tokens."""
    if len(tokens) == 0:
        return
        # raise SyntaxError('unexpected EOF') # is this OK?
    token = tokens.pop(0)
    if token == '(':
        L = []
        while tokens[0] != ')':
            L.append(read_from_tokens(tokens))
        tokens.pop(0)  # pop off ')'
        return L
    elif token == ')':
        raise SyntaxError('unexpected )')
    else:
        return atom(token)


def atom(token: str) -> Atom:
    """Numbers become numbers; every other token is a symbol."""
    try:
        return int(token)
    except ValueError:
        try:
            return float(token)
        except ValueError:
            return Symbol(token)




# here
import argparse

g_bitvector_width = 64
g_bitvector_signedness = "signed"


def rep_operand(op: str) -> str:
    if g_bitvector_signedness == "signed":
        rep_rules = {
            "+": "bvadd",
            "-": "bvsub",
            "*": "bvsmul",
            "%": "bvsdiv",
            "div": "bvsdiv",
            ">=": "bvsge",
            "<=": "bvsle",
            ">": "bvsgt",
            "<": "bvslt",
            "mod": "bvsmod",
            "rem": "bvsrem",
            "Int": "(_ BitVec {})".format(g_bitvector_width),
            "AUFLIA": "AUFBV",
            "UFLIA": "UFBV",
        }

    else:
        rep_rules = {
            "+": "bvadd",
            "-": "bvsub",
            "*": "bvumul",
            "%": "bvudiv",
            "div": "bvudiv",
            ">=": "bvuge",
            "<=": "bvule",
            ">": "bvugt",
            "<": "bvult",
            "mod": "bvumod",
            "rem": "bvurem",
            "Int": "(_ BitVec {})".format(g_bitvector_width),
            "AUFLIA": "AUFBV",
            "UFLIA": "UFBV",
        }
    if op in rep_rules:
        return rep_rules[op]
    return op


def to_bv_sexpr_misc(line: list[str]):
    """
    This is used for converting LIRA expressions to BV
    E.g.,
    ['and', ['=', 'x', 1], ['=', 'y', 1]]
    ['and', ['=', 'x!', ['+', 'x', 'y']], ['=', 'y!', ['+', 'x', 'y']]]
    """
    res = ["("]
    if not isinstance(line[0], list):
        if (
            line[0] == "-" and len(line) == 2 and (not isinstance(line[1], list))
        ):  # ['-', 50]
            """
            Consider  x == -50, i.e., ['=', 'x', ['-', 50]]
            https://stackoverflow.com/questions/37044372/how-to-present-negative-number-in-bitvector
            This is usually done via two's complement encoding. The short version is,
                   -x = flip(x) + 1
                   where flip(x) simply flips all the bits in x. NOTE: flip is  (bvnot x) in SMT-LIB

             According to the above discussion,  ['-', 50] should be converted to
                      ['bvadd', 1, [bvnot', 50]]
            """
            if isinstance(line[1], int):
                var = "(_ bv{} {})".format(line[1], g_bitvector_width)
            else:
                var = line[1]
            new_line = ["bvadd", "(_ bv1 {})".format(g_bitvector_width), ["bvnot", var]]
        else:
            new_line = [rep_operand(line[0])]
            new_line += line[1:]
    else:
        new_line = line

    for element in new_line:
        # print("element: ",element)
        if isinstance(element, list) and len(element) > 0:
            # rep operand
            if not isinstance(element[0], list):
                # handling cases like x = -50 (same as above)
                if (
                    element[0] == "-"
                    and len(element) == 2
                    and (not isinstance(element[1], list))
                ):  # ['-', 50]
                    if isinstance(element[1], int):
                        var = "(_ bv{} {})".format(element[1], g_bitvector_width)
                    else:
                        var = element[1]
                    new_element = [
                        "bvadd",
                        "(_ bv1 {})".format(g_bitvector_width),
                        ["bvnot", var],
                    ]
                else:
                    new_element = [rep_operand(element[0])]
                    new_element += element[1:]
            else:
                new_element = element

            for exp in to_bv_sexpr_misc(new_element):
                res.append(exp)
        elif isinstance(element, list) and len(element) == 0:
            res.append("()")
        else:
            # replace int with bv
            if isinstance(element, int):
                res.append("(_ bv{} {})".format(element, g_bitvector_width))
            else:
                res.append(rep_operand(str(element)))
    res.append(")")
    return res


def ira2bv(tt: str) -> str:
    parse_re: list = parse_sexpression(tt)
    # print(parse_re)
    bv_re = [" ".join(to_bv_sexpr_misc(line)) for line in parse_re]
    return "\n".join(bv_re)


if __name__ == "__main__":
    arg_p = argparse.ArgumentParser()
    arg_p.add_argument("file", help="Input file")
    args = arg_p.parse_args()
    with open(args.file, "r") as f:
        content = f.read()
    content = "(" + content + ")"
    fml_str = ira2bv(content)
    print(fml_str)

