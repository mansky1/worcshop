# -*- coding: utf-8 -*-

import re

Ident = "([a-zA-Z_][a-zA-Z0-9_]*)"
WS = r"(\s)+"
WS0 = r"(\s)*"
TypeSpecNormal = f"({Ident}{WS0})+"
TypeSpecPtr = f"{TypeSpecNormal}(\\*{WS0})+"
TypeSpec = f"(({TypeSpecNormal}{WS})|({TypeSpecPtr}{WS0}))"
Param = f"{TypeSpec}{Ident}"
Params = f"(({Param}({WS0},{WS0}{Param})*)|void)"
ParamTypes = f"{TypeSpec}({WS0},{WS0}{TypeSpec})*"
FunHeadPat = re.compile(f"{WS0}(?P<rtype>{TypeSpec})(?P<fname>{Ident}){WS0}\\(({WS0}{Params})?{WS0}\\){WS0}")
ParamPat = re.compile(f"{WS0}(?P<type>{TypeSpec}){Ident}{WS0}")
CompositeStartPat = re.compile(f"{WS0}(struct|union|enum){WS}{Ident}{WS0}\\{{")

# int foo(int a, int b) -> int foo(int, int); int a; int b; int __return;
# void bar(int a, int b) -> void bar(int, int); int a; int b;
def process_funhead(funhead_match: re.Match):
    s = funhead_match.group()
    decls_str = s[s.find('(') + 1 : s.find(')')].strip()
    if decls_str == '' or decls_str == 'void':
        params = []
    else:
        params = decls_str.split(',')
    grpdict = funhead_match.groupdict()

    fun_decl = grpdict['rtype'] + " " + grpdict['fname'] + '('
    if len(params) >= 1:
        fun_decl += re.fullmatch(ParamPat, params[0]).groupdict()['type']
        for p in params[1:]:
            fun_decl += ',' + re.fullmatch(ParamPat, p).groupdict()['type']
    elif decls_str == 'void':
        fun_decl += 'void'
    fun_decl += ');'

    param_decls = list(map(lambda s: s + ';', params))

    rettype = grpdict['rtype']
    if re.fullmatch(f"{WS0}void{WS0}", rettype):
        ret_decl = []
    else:
        ret_decl = [rettype + " __return;"]

    return [fun_decl] + param_decls + ret_decl

def process_return(return_match: re.Match):
    s = return_match.group()
    ret_idx = s.find('return')
    return ["__return = " + s[ret_idx + 6 : ]]

# find the index of the ')' matching the first '(' in s[base:]
def match_paren(s: str, base: int):
    cnt = 0
    for i in range(base, len(s)):
        if s[i] == '(':
            cnt += 1
        elif s[i] == ')':
            assert(cnt > 0)
            if cnt == 1:
                return i
            else:
                cnt -= 1
    raise Exception("() not match!")

# find the index of the '}' matching the first '{' in s[base:]
def match_brace(s: str, base: int):
    cnt = 0
    for i in range(base, len(s)):
        if s[i] == '{':
            cnt += 1
        elif s[i] == '}':
            assert(cnt > 0)
            if cnt == 1:
                return i
            else:
                cnt -= 1
    raise Exception("{} not match!")

def have_prefix(s: str, prefix: str):
    l = len(prefix)
    return len(s) >= l and s[0:l] == prefix

# return the index of end of the next ps in s
# and list of partial statement to be executed
# ignore [0 : base]
def segment_process_ps(s: str, base: int, funhead2decl=True) -> tuple:
    length = len(s)
    while base < length and s[base].isspace():
        base += 1
    if base == length:
        return (length - 1, [""])
    
    prefix_tmp = s[base:]

    composite_match = re.match(CompositeStartPat, prefix_tmp)

    if composite_match:
        _, end = composite_match.span()
        lbrace_offset = end - 1
        rbrace_offset = match_brace(prefix_tmp, lbrace_offset)
        semic_idx = s.find(';', base + rbrace_offset + 1)
        return (semic_idx, [s[base : semic_idx + 1]])
    elif have_prefix(prefix_tmp, '{') or have_prefix(prefix_tmp, '}'):
        return (base, [s[base]])
    elif have_prefix(prefix_tmp, 'else'):
        return (base + 3, [s[base : base + 4]])
    elif have_prefix(prefix_tmp, 'while'):
        p_idx = match_paren(s, base)
        return (p_idx, [s[base : p_idx + 1]])
    elif have_prefix(prefix_tmp, 'for'):
        p_idx = match_paren(s, base)
        return (p_idx, [s[base : p_idx + 1]])
    elif have_prefix(prefix_tmp, 'if'):
        p_idx = match_paren(s, base)
        return (p_idx, [s[base : p_idx + 1]])
    elif have_prefix(prefix_tmp, '//@'):
        newline_idx = s.find('\n', base)
        if newline_idx == -1: # line comment terminated by EOF
            return (length - 1, s[base:])
        else:
            return (newline_idx - 1, [s[base : newline_idx + 1]])
    elif have_prefix(prefix_tmp, '/*@'):
        end_idx = s.find('*/', base)
        if end_idx == -1:
            raise Exception("comment not finished!")
        else:
            ass_str = s[base + 3 : end_idx]
            if re.match(f"{WS0}Let", ass_str):
                return (end_idx + 1, "")
            else:
                return (end_idx + 1, [s[base : end_idx + 2]])
    elif have_prefix(prefix_tmp, '//'):
        newline_idx = s.find('\n', base)
        if newline_idx == -1: # line comment terminated by EOF
            return (length - 1, "")
        else: # skip plain comment
            next_start_index = newline_idx + 1
            return segment_process_ps(s, next_start_index)
    elif have_prefix(prefix_tmp, '/*'):
        end_idx = s.find('*/', base)
        if end_idx == -1:
            raise Exception("comment not finished!")
        else: # skip plain comment
            next_start_index = end_idx + 2
            return segment_process_ps(s, next_start_index)
    else:
        funhead_match = re.match(FunHeadPat, prefix_tmp)
        if funhead_match:
            (_, end) = funhead_match.span()
            if funhead2decl:
                return (base + end - 1, process_funhead(funhead_match))
            else:
                return (base + end - 1, [s[base : base + end]])
        semi_idx = s.find(';', base)
        lbrace_idx = s.find('{', base)
        if semi_idx == -1:
            if lbrace_idx == -1:
                raise Exception("invalid statement")
            else:
                end_idx = lbrace_idx - 1
        else:
            if lbrace_idx == -1:
                end_idx = semi_idx
            else:
                if semi_idx < lbrace_idx:
                    end_idx = semi_idx
                else:
                    end_idx = lbrace_idx - 1
        return (end_idx, [s[base : end_idx + 1]])