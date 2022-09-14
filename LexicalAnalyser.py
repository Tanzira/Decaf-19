#!/usr/bin/env python
# -*- coding: utf-8 -*- 
from __future__ import unicode_literals
from Scanner import *
import sys
from decimal import Decimal
def lexical_analysis(raw_input = '', isFile = True):
    MAXIDENLEN = 31
    if isFile:
        inputFile = sys.argv[1]
        with open(inputFile,'r') as i:
            raw_input = i.read()

    lexer = process_input(raw_input)
    col_st = 1
    col_nd = 1
    prev_line = 0
    list_of_tokens = []
    while True:
        tok = lexer.token()
        if not tok: 
            break      # No more input
        token_length = len(str(tok.value))
        
        if prev_line < tok.lineno:
            prev_line = tok.lineno
            col_st = 1  
        else:
            col_st = col_nd + 1
        if tok.type == 'TAB':
            token_length = 8 - col_st + 1
        col_nd = col_st + token_length - 1
        list_of_tokens.append({'value' : tok.value, 'type' : tok.type, 'lineno' : tok.lineno, 'col_st' : col_st, 'col_nd': col_nd})
        '''
        if tok.type == 'OP':
            print("{} \t line {} cols {}-{} is '{}'.".format(tok.value, tok.lineno, col_st, col_nd, tok.value))
        elif tok.type == 'UNTERMINATED_STRING':
            print("\n*** Error line {} \n*** Unterminated string constant:{} \n".format(tok.lineno, tok.value))
        elif tok.type == 'HASH':
            print("\n*** Error line {} \n*** Invalid # directive\n".format(tok.lineno))
        #elif tok.type == 'SINGLELINE_COMMENT':

        elif tok.type == 'T_IntConstant':
            print("{}\t line {} cols {}-{} is T_IntConstant (value = {})".format(tok.value, tok.lineno, col_st, col_nd, int(tok.value)))
        #elif tok.type == 'MULTILINE_COMMENT':
        elif tok.type == 'T_StringConstant':
            print("{}\t line {} cols {}-{} is T_StringConstant (value = {})".format(tok.value, tok.lineno, col_st, col_nd, tok.value))
        elif tok.type == 'T_BoolConstant':
            print("{}\t line {} cols {}-{} is T_BoolConstant (value = {})".format(tok.value, tok.lineno, col_st, col_nd, tok.value))
        elif tok.type == 'T_DoubleConstant':
            val = float(tok.value)
            result = '{0:.6g}'.format(val)
            print("{}\t line {} cols {}-{} is T_DoubleConstant (value = {})".format(tok.value, tok.lineno, col_st, col_nd, result))
        elif tok.type == 'T_Identifier':
            if token_length > MAXIDENLEN:
                print("\n*** Error line {}.\n*** Identifier too long: \"{}\"\n".format(tok.lineno, tok.value))
                print("{}\t line {} cols {}-{} is T_Identifier (truncated to {})".format(tok.value, tok.lineno, col_st, col_nd, tok.value[0:31]))
            else:
                print("{}\t line {} cols {}-{} is T_Identifier".format(tok.value, tok.lineno, col_st, col_nd))
        elif tok.type == 'SPACE':
            pass
        else:
            print("{} \t line {} cols {}-{} is {}.".format(tok.value, tok.lineno, col_st, col_nd, tok.type))
    #print(list_of_tokens)
    '''
    list_of_tokens.append({'value' : '$', 'type' : 'T_EOF', 'lineno' : list_of_tokens[-1]['lineno'], 'col_st' : 1, 'col_nd': 1})
    return list_of_tokens, raw_input
#lexical_analysis()