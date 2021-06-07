# Author: Huihui Xu
# Inference rule: resolution algorithm
# 1. Convert KB to the CNF form;
# 2. Apply iteratively the resolution rule starting from KB, neg theorem
# 3. Stop when: Contradiction is reached then proves entailments
# 4. or no more new sentences can be derived then disproves it

import sys
import re
from itertools import combinations


# read input file
kb = []
def in_put(file):
    #load input file and store kb in a list
    sentences = []
    output_file = "output.txt"
    try:
        input_file = open(file,"r")
        lines = input_file.readlines()
        for idx, line in enumerate(lines):
            line = line.strip("\n")
            sentences.append(line)
    except IOError:
        output_file = open(output_file, "w")
        output_file.write("File not found: {}".format(file))
        output_file.close()
        sys.exit()
    return sentences

def check_simple(sentence):
    # if it is a literal
    components = sentence.split(" ")
    if len(components) < 4 and "(" not in sentence:
        return True
    else:
        return False

def check_conjucts(s):
    # check if sentence is a simple conjuct
    # if so, extract all the variables for further usage
    # if not, return the way it is
    if "&" in s:
        variables = re.findall(r'~?\w', s)
        return variables
    else:
        return s

def split_eq(s):
    # when "<=>" in a sentence, it can be splitted into two parts
    if "<=>" in s:
        elimination = eliminate_implications(s)
        # cut in the middle
        #print(elimination)
        mid = int((len(elimination)+1)/2)
        term1 = elimination[:mid-1].strip()
        #print(term1)
        term2 = elimination[mid+1:].strip()
        #print(term2)
    return term1, term2

def negation(s):
    # negate a simple or complicated sentence
    # if there are brackets

    if "~" in s:
        # perform double negation
        s = re.sub('~','',s)
        return s
    else:
        return "~"+s

def split_sentence(sentence, op):
    # split a complicated sentence based on the operator
    splits = sentence.split(op)
    return splits

def eliminate_implications(sentence):
    # change >>  into &, |, or ~
    # eliminate_implications(P >> R)
    # ~P | R
    if ">>" in sentence:
        splits = split_sentence(sentence, ">>")
        a = splits[0].strip()
        b = splits[1].strip()
        result = "~"+a +" | "+b

    else:
        splits = split_sentence(sentence, "<=>")
        a = splits[0].strip()
        b = splits[1].strip()
        result = "(~"+a + " | "+b+")"+" & "+"(~"+b+" | "+a+")"
        #print(len(result))
    return result

def extract_scopes(sentence):
    # extract all the quotated sentences
    scopes = re.findall(r'~?\(.*?\)', sentence)
    return scopes

def de_morgan(s):
    #apply the De Morgan Law
    # moving negation symbol
    # de_morgan(~(A | B))
    # (~A & ~B)
    # scopes = extract_scopes(s)
    # for scope in scopes:
        # find the pattern for de morgan law
    if "~" in s: # if pattern exist
        variables = re.sub(r'\W+',' ',s)
        variables = variables.strip()
        variables = [v.strip() for v in variables.split(' ')]
        variables = [negation(v) for v in variables]
        if "|" in s:
            # only find all the variables
            new_formula = variables[0] + " & "+variables[1]
        else: # while "&" in the scope
            new_formula = variables[0]+" | "+variables[1]
    else:
        pass
    return new_formula

def distributive(s): # only exists when the sentence is complicated
    # distributive(B | (A & C))
    # (B | A) & (B | C)
    if "&" in s and "|" in s:
        # will use distributive law
        # and being splited into two parts
        splits = s.split("|")
        for split in splits:
            if "&" not in split:
                keep_part = split.strip()
            else:
                distr_part = split.strip()
        # clean up the distr_part
        distr_part = re.sub(r"\W+"," ", distr_part).strip()
        variables = [v.strip() for v in distr_part.split(' ')]
        new_terms = []
        for v in variables:
            new_term = "("+keep_part + " | " + v+")"
            new_terms.append(new_term)
        result = new_terms[0] + " & " + new_terms[1]
    return result



def to_cnf(s):
# convert a sentence to CNF: conjunction of clauses
# while clauses includes disjuctions of literals
    if not isinstance(s, str):
        print("Please input a string!")
        return
    else:
        # if it is a simple sentence
        simple_flag = check_simple(s)
        if simple_flag:
            if "|" in s:
                return s
            elif "&" in s:
                # if it is a simple conjunct, then return variables
                variables = check_conjucts(s)
                return variables
            elif ">>" in s:
                # if it is a simple implication, then return cnf
                cnf = eliminate_implications(s)
                return cnf
            elif "<=>" in s:
                cnf = eliminate_implications(s)
                return cnf
            else:
                return s
        else: # if it is not a simple sentence
            if "~" in s:
                result = de_morgan(s)
                if '&' in result:
                    result = check_conjucts(result)
            elif "&" in s and "|" in s:
                result = distributive(s)
            return result


def resolve(ci,cj):
    clauses = []
    dis_ci = disjuncts(ci)
    dis_cj = disjuncts(cj)
    # print("ci:" + ci)
    # print("cj:" + cj)
    for di in dis_ci:
        #print("di:" + di)
        for dj in dis_cj:
            #print("dj:"+dj)
            if di == negation(dj) or negation(di) == dj:

                dnew = unique(remove_sub(disjuncts(ci),di) + \
                remove_sub(disjuncts(cj),dj))
                clauses.append(dnew)

    return clauses

def union(s):
    if len(s) > 1:
        result = s[0] + " "
        for i in range(1,len(s)):
            result += "| "+s[i]
        return result
    else:
        return s

def resolution(kb, alpha):
    # kb: knowledge base and sentence are converted into CNF
    # alpha : the conclusion/theorem needed to be proved
    neg_alpha = negation(alpha)
    #kb.append(neg_alpha)
    kb = set(kb)
    # negate the theorem
    new = set()
    # print("original kbs:")
    # print(kb)
    while True:
        n = len(kb)
        old_l = len(kb)
        pairs = list(combinations(kb, 2))
        # print("all pairs:")
        # print(pairs)

        # store idx of pair that has reslovents
        resoluted_kbs = set()
        for idx, pair in enumerate(pairs):
            resolvents = resolve(pair[0], pair[1])
            # if exists reslovents
            # print("resolvents")
            # print(resolvents)
            if len(resolvents):
                resoluted_kbs.add(pair[0])
                resoluted_kbs.add(pair[1])

                for r in resolvents:
                    if len(r) > 1:
                        new_union = str(union(r))
                    elif len(r) ==1:
                        new_union = str(r[0])
                # if False in resolvents:
                #     return True
                new.add(new_union)

        if set(alpha).issubset(kb):
            return True
        for n in new:
            kb.add(n)
        new_l = len(kb)
        if old_l == new_l:
            return False

def disjuncts(s):
    # return a list of the disjuncts in the sentence
    if "|" in s:
        return split_sentence(s, " | ")
    else:
        return [s]

def remove_sub(s, sub):
    """Return a copy of seq (or string) with all occurences of item removed.
    >>> removeall(3, [1, 2, 3, 3, 2, 1, 3])
    [1, 2, 2, 1]
    >>> removeall(4, [1, 2, 3])
    [1, 2, 3]
    """
    if isinstance(s, str):
        return s.replace(sub, '')
    else:
        return [x for x in s if x != sub]

def unique(s):
    """Remove duplicate elements from seq. Assumes hashable elements.
    >>> unique([1, 2, 3, 2, 1])
    [1, 2, 3]
    """
    return list(set(s))

file_name = sys.argv[1]
alpha = sys.argv[2]

if alpha != alpha.upper():
    print("Please input an uppercase letter as a theorem!")
else:
    ss = in_put(file_name)
    print(ss)
    kb = set()
    for s in ss:
        cnf_s = to_cnf(s)
        if isinstance(cnf_s, list):
            for c in cnf_s:
                kb.add(c)
        else:
            kb.add(cnf_s)

    print("The knowledge base:")
    print(kb)
    result = resolution(kb, alpha)
    print(result)
