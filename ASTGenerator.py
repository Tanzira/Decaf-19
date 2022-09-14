
#!/usr/bin/env python
# -*- coding: utf-8 -*- 
from __future__ import unicode_literals
from abc import ABC
from Scanner import process_input
from LexicalAnalyser import lexical_analysis
pos = 0

ALL_TYPES = ['T_Int', 'T_Bool', 'T_String', 'T_Double']
VOID = ['T_Void']
ALL_CONSTANTS = ['T_StringConstant', 'T_BoolConstant' ,'T_DoubleConstant', 'T_IntConstant', 'T_Null']
OP_ARITHMETIC = ['+', '-', '*', '/', '%']
OP_RELATIONAL = ['>', '<', '>=', '<=', '!=', '==']
OP_LOGICAL = ['&&', '||']
KEYWORD_EXPR = {'T_ReadInt': 'ReadIntegerExpr: ', 'T_ReadLine' : 'ReadLineExpr: '}
WHITE_SPACE = ['SPACE', 'TAB']

class DecafSyntaxError(SyntaxError):
    def __init__(self, message, lineno, col_st, col_nd):
        self.message = message
        self.lineno = lineno
        self.col_st = col_st
        self.col_nd = col_nd

class EStr(str):
    def __init__(self, value):
        self.value = value
        self.reg = None
    def set_position(self, token):
        self.col_st = token['col_st']
        self.col_nd = token['col_nd']
        self.lineno = token['lineno']
        self.line_nd = token['lineno']
    
    

class ASTNode(ABC):
    def __init__(self):
        self.symbol_table = None
        self.lineno = -1
        self.col_st = -1
        self.col_nd = -1
        self.line_nd = -1
    def set_position(self, token):
        self.col_st = token['col_st']
        self.col_nd = token['col_nd']
        self.lineno = token['lineno']
        self.line_nd = token['lineno']
    def inherit_position(self, col_st, col_nd, lineno, line_nd):
        self.col_st = col_st
        self.col_nd = col_nd
        self.lineno = lineno
        self.line_nd = line_nd

class Program(ASTNode):
    def __init__(self):
        self.decls = []
    def add(self, decl):
        self.decls.append(decl)
    def add_all(self, decls):
        for decl in decls:
            self.add(decl)
    def print_self(self):
        print("Program: ")
        for decl in self.decls:
            t = 1
            decl.print_self(t)

class Decl(ASTNode):
    pass

class VariableDecl(Decl):
    def __init__(self, variable):
        self.variable = variable
    def print_self(self, tab = 0):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + "VarDecl: ")
        self.variable.print_self(t+1)

class Variable(ASTNode):
    def __init__(self, v_type, ident):
        self.v_type = v_type
        self.ident = ident
    def print_self(self, tab = 0):
        t, ts = tab, ''.join('    ' * tab)
        self.v_type.print_self(t, prefix = "")
        print(ts + "Identifier: " + self.ident)
    
class FunctionDecl(Decl):
    def __init__(self, type_a, ident, formals, stmtblock):
        self.type_a = type_a
        self.formals = formals
        self.ident = ident
        self.stmtblock = stmtblock
        
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + "FnDecl: ")
        self.type_a.print_self(t + 1, prefix = "(return type) ")
        print(ts + ts + "Identifier: " + self.ident)
        self.formals.print_self(t+1, prefix = "(formals) ")
        self.stmtblock.print_self(t+1, prefix = "(body) ")


class Formals(ASTNode):
    def __init__(self):
        self.variables = []
    def add(self, variable):
        self.variables.append(variable)
    def add_all(self, variables):
        for variable in variables:
            self.add(variable)
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        for variable in self.variables:
            print(ts + prefix + "VarDecl: ")
            variable.print_self(t+1)
    
class Stmt(ASTNode):
    def print_self(self, tab = 0, prefix = ""):
        pass

class StmtBlock(Stmt):
    def __init__(self):
        self.variable_decls = []
        self.stmts = []
    def add_var_decl(self, variable_decl):
        self.variable_decls.append(variable_decl)
    def add_all_var_decls(self, variable_decls):
        for variable_decl in variable_decls:
            self.add_var_decl(variable_decl)
    def add_stmt(self, stmt):
        self.stmts.append(stmt)
    def add_all_stmt(self, stmts):
        for stmt in stmts:
            self.add_stmt(stmt)
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + prefix + "StmtBlock: ")
        for var_decl in self.variable_decls:
            var_decl.print_self(t+1)
        for stmt in self.stmts:
            if stmt != None:
                stmt.print_self(t+1)

class ExprStmt(Stmt):
    def __init__(self, expr = None):
        self.expr = expr
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        if self.expr != None:
            self.expr.print_self(t, prefix)
    

class IfStmt(Stmt):
    def __init__(self, test_expr, then_stmt, else_stmt = None):
        self.test_expr = test_expr
        self.then_stmt = then_stmt
        self.else_stmt = else_stmt

    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + "IfStmt: ")
        self.test_expr.print_self(tab+1, "(test) ")
        self.then_stmt.print_self(t+1, "(then) ")
        if self.else_stmt != None:
            self.else_stmt.print_self(t+1, "(else) ")

class WhileStmt(Stmt):
    def __init__(self, test_expr, then_stmt):
        self.test_expr = test_expr
        self.then_stmt = then_stmt

    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + "WhileStmt: ")
        self.test_expr.print_self(t+1, "(test) ")
        self.then_stmt.print_self(t+1, "(body) ")

class ForStmt(Stmt):
    def __init__(self, expr_test, stmt, expr_init = None, expr_inc = None):
        self.expr_test = expr_test
        self.stmt = stmt
        self.expr_init = expr_init
        self.expr_inc = expr_inc

    def print_self(self, tab = 0, prefix = ''):
        t, ts = tab, ''.join('    ' * tab)
        ts2 = ''.join('    ' * (tab+1))
        print(ts + "ForStmt: ")
        if self.expr_init != None:
            self.expr_init.print_self(t+1, "(init) ")
        else:
            print(ts2 + "(init) Empty:")
        self.expr_test.print_self(t+1, "(test) ")
        if self.expr_inc != None:
            self.expr_inc.print_self(t+1, "(step) ")
        else:
            print(ts2 + "(step) Empty:")
        self.stmt.print_self(t+1, "(body) ")

class BreakStmt(Stmt):
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + prefix+ "BreakStmt: ")

class PrintStmt(Stmt):
    def __init__(self):
        self.exprs = []
    def add(self, expr):
        self.exprs.append(expr)
    def add_all(self, exprs):
        for expr in exprs:
            self.add(expr)
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + prefix+ "PrintStmt: ")
        for expr in self.exprs:
            expr.print_self(t+1, "(args) ")

class ReturnStmt(Stmt):
    def __init__(self, expr = None):
        self.expr = expr
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        ts2 = ''.join('    ' * (tab+1))
        print(ts + prefix+ "ReturnStmt: ")
        if self.expr != None:
            self.expr.print_self(t+1)
        else:
            print(ts2 + "Empty: ")
'''
{} means 0 or more
E  ::= LValue= E1 | E1
E1 ::= E2 {LogicalOr E2}
LogicalOr ::= ||
E2 ::= E3 {LogicalAnd E3}
LogicalAnd ::= &&
E3 ::= E4 {EqualityExpr E4}
EqualityExpr ::= == | !=
E4 ::= E5 {RelationalExpr E5}
RelationalExpr ::= < | <= | > | >=
E5 ::= E6 {ArithmaticOperator E6}
ArithmaticOperator ::= + | -
E6 ::= E7 {Prod E7}
Prod ::= *| / | %
E7 ::= <UnaryOperator> E7 | Lvalue | (E) | Constant | Call | ReadInteger() | ReadLine()
UnaryOperator ::= ! | -

'''
class Expression(ASTNode):
    def __init__(self):
        self.reg = None
        self.e_type = None

class E(Expression):
    def __init__(self, lvalue = None, e1 = None, op_str = None ):
        self.e1 = e1
        self.lvalue = lvalue  
        self.op_str = op_str
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        ts2 = ''.join('    ' * (tab +1 ))
        if self.lvalue != None:
            print(ts + prefix+ "AssignExpr: ")
            self.lvalue.print_self(t+1, "")
            print(ts2 + "Operator: =")
            self.e1.print_self(t+1)
        else:
            self.e1.print_self(t, prefix)

class EBinary(Expression):
    def __init__(self, e_left, op, label, e_right):
        self.e_left = e_left
        self.op = op
        self.label = label
        self.e_right = e_right
        #self.e_type = None

    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        ts2 = ''.join('    ' * (tab+1))
        print(ts + prefix + self.label)
        self.e_left.print_self(t+1, "")
        print(ts2 +  "Operator: " + self.op)
        self.e_right.print_self(t+1, "")


class E7(Expression):
    def print_self(self, tab = 0, prefix = ""):
        pass

class E7Unary(E7):
    def __init__(self, op, label, e):
        self.op = op
        self.label = label
        self.e = e
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        ts2 = ''.join('    ' * (tab+1))
        print(ts + prefix + self.label)
        print(ts2 + "Operator: " + self.op)
        self.e.print_self(t+1, "")

class E7Keyword(E7):
    def __init__(self, k):
        self.k = k
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + prefix + self.k)

class E7Member(E7):
    def __init__(self, member):
        self.member = member
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        self.member.print_self(t, prefix)

class LValue(Expression):
    def __init__(self, ident):
        self.ident = ident
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        ts2 = ''.join('    ' * (tab + 1))
        print(ts + prefix + "FieldAccess: ")
        print(ts2 + "Identifier: " + self.ident)

class Call(E7):
    def __init__(self, ident, actuals):
        self.actuals = actuals
        self.ident = ident
    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        ts2 = ''.join('    ' * (tab + 1))
        print(ts + prefix + "Call: ")
        print(ts2 + "Identifier: " + self.ident)
        self.actuals.print_self(t+1, "")
        
class Actuals(ASTNode):
    def __init__(self):
        self.exprs = []
    def add(self, expr):
        self.exprs.append(expr)
    def add_all(self, exprs):
        for expr in exprs:
            self.add(expr)
    def print_self(self, tab = 0, prefix = ""):
        for e in self.exprs:
            e.print_self(tab, "(actuals) ")

class Constant(Expression):
    def __init__(self, c_type, c_value):
        self.c_type = c_type
        self.c_value = c_value
        self.e_type = None

    def print_self(self, tab = 0, prefix = ""):
        t, ts = tab, ''.join('    ' * tab)
        print(ts + prefix + self.c_type.t_type + ": " + self.c_value)

class TypeAny(ASTNode):
    def __init__(self):
        self.type = ""
        self.tval = ""

class Void(TypeAny):
    def __init__(self):
        self.t_type = 'Void'
        self.t_val = "void"
    
    def print_self(self, tab = 0, prefix = ""):
        ts = ''.join('    ' * tab)
        print(ts+ prefix+ "Type: " + self.t_val)

class Type(TypeAny):
    def __init__(self, t_type, t_val):
        self.t_type = t_type
        self.t_val = t_val
    
    def print_self(self, tab = 0, prefix = ""):
        ts = ''.join('    ' * tab)
        print(ts+ prefix + "Type: " + self.t_val)


        
def raise_decaf_error(token_stream):
    global pos
    message = "*** syntax error"
    col_st = token_stream[pos]['col_st']
    col_nd = token_stream[pos]['col_nd']
    lineno = token_stream[pos]['lineno']
    se = DecafSyntaxError(message, lineno, col_st, col_nd)
    raise se

'''Program ::= Decl+'''
#scope creation
def get_program(token_stream):
    global pos
    if check_token_type(token_stream, 'T_EOF'): 
        program = Program()
        return program
    else:
        decl = get_decl(token_stream)
        program = Program()
        program.add(decl)
        rest_prog = get_program(token_stream)
        program.add_all(rest_prog.decls)
        return program

'''Decl ::= VariableDecl | FunctionDecl'''
def get_decl(token_stream):
    global pos
    if token_stream[pos]['type'] in ALL_TYPES or token_stream[pos]['type'] in VOID:
        tok_type = get_type_any(token_stream)
        ident = get_ident(token_stream)
        if check_token(token_stream, ';') and isinstance(tok_type, Type):
            next_token(token_stream, ';')
            variable = Variable(tok_type, ident)
            variable_decl = VariableDecl(variable)
            return variable_decl
        elif check_token(token_stream, '('):
            next_token(token_stream, '(')
            formals = get_formals(token_stream)
            next_token(token_stream, ')')
            stmtblock = get_stmtblock(token_stream, False)
            fn_decl = FunctionDecl(tok_type, ident, formals, stmtblock)
            
            return fn_decl
        else:
            raise_decaf_error(token_stream)
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return get_decl(token_stream)
    else:
        raise_decaf_error(token_stream)

'''Variable ::= Type ident'''
def get_var_decl(token_stream):
    tok_type = get_type(token_stream)
    ident = get_ident(token_stream)
    next_token(token_stream, ';')
    variable = Variable(tok_type, ident)
    return VariableDecl(variable)
      
''' Formals::= Variable+ , | ε '''
def get_formals(token_stream):
    global pos
    if token_stream[pos]['type'] in ALL_TYPES:
        formals = Formals()
        formals.add(get_variable(token_stream))
        rest_formals = get_formals_rest(token_stream)
        formals.add_all(rest_formals.variables)
        return formals
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return get_formals(token_stream)
    elif token_stream[pos]['value'] == ')':
        return Formals()
    else:
        raise_decaf_error(token_stream)

def get_formals_rest(token_stream):
    global pos
    if token_stream[pos]['value'] == ',':
        next_token(token_stream, ',')
        if token_stream[pos]['value'] in ALL_TYPES or token_stream[pos]['type'] == 'SPACE':
            return get_formals(token_stream)
        else:
            raise_decaf_error(token_stream)
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return get_formals_rest(token_stream)
    elif token_stream[pos]['value'] == ')':
        return Formals()
    else:
        raise_decaf_error(token_stream)

'''Variable ::= Type ident'''
def get_variable(token_stream):
    global pos
    if token_stream[pos]['type'] in ALL_TYPES:
        tok_type = get_type(token_stream)
        ident = get_ident(token_stream)
        #insert into symbol table
        variable = Variable(tok_type, ident)
        return variable
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return get_variable(token_stream)
    else:
        raise_decaf_error(token_stream)

'''StmtBlock::= { VariableDecl∗ Stmt∗ }'''
#scope creation
def get_stmtblock(token_stream, create_scope = True):
    global pos
    next_token(token_stream, '{')
    var_decls, stmts = [], []
    if check_token(token_stream, '}'):
        next_token(token_stream, '}')
        return StmtBlock()
    while token_stream[pos]['type'] in ALL_TYPES:
        var_decls.append(get_var_decl(token_stream))
        while token_stream[pos]['type'] in WHITE_SPACE:
            pos += 1
    while not check_token(token_stream, '}'):
        stmts.append(get_stmt(token_stream))
    next_token(token_stream, '}')    
    stmtblock = StmtBlock()
    stmtblock.add_all_var_decls(var_decls)
    stmtblock.add_all_stmt(stmts)
    return stmtblock

'''Stmt::= <Expr>; | IfStmt | WhileStmt | ForStmt 
| BreakStmt | ReturnStmt | PrintStmt | StmtBlock'''
def get_stmt(token_stream):
    if check_token(token_stream, 'if'):
        return get_if_stmt(token_stream)
    elif check_token(token_stream, 'while'):
        return get_while_stmt(token_stream)
    elif check_token(token_stream, 'for'):
        return get_for_stmt(token_stream)
    elif check_token(token_stream, 'break'):
        return get_break_stmt(token_stream)
    elif check_token(token_stream, 'return'):
        return get_return_stmt(token_stream)
    elif check_token(token_stream, 'Print'):
        return get_print_stmt(token_stream)
    elif check_token(token_stream, '{'):
        return get_stmtblock(token_stream)
    else:
        #debug_stream(token_stream)
        expr_stmt = ExprStmt()
        if not check_token(token_stream, ';'):
            expr_stmt = ExprStmt(get_e(token_stream))
            next_token(token_stream, ';')
        else:
            next_token(token_stream, ';')
        return expr_stmt
    return Stmt()

'''IfStmt::= if ( Expr ) Stmt <else Stmt>'''
def get_if_stmt(token_stream):
    global pos
    next_token(token_stream, 'if')
    next_token(token_stream, '(')
    test_expr = get_e(token_stream)
    next_token(token_stream, ')')
    then_expr = get_stmt(token_stream)
    if check_token(token_stream, 'else'):
        next_token(token_stream, 'else')
        else_expr = get_stmt(token_stream)
        return IfStmt(test_expr, then_expr, else_expr)
    else:
        return IfStmt(test_expr, then_expr)

'''WhileStmt::= while ( Expr ) Stmt'''
def get_while_stmt(token_stream):
    next_token(token_stream, 'while')
    next_token(token_stream, '(')
    test_expr = get_e(token_stream)
    next_token(token_stream, ')')
    then_stmt = get_stmt(token_stream)
    return WhileStmt(test_expr, then_stmt)

'''ForStmt::= for ( <Expr>; Expr ; <Expr>) Stmt'''
def get_for_stmt(token_stream):
    global pos
    next_token(token_stream, 'for')
    next_token(token_stream, '(')
    expr_init, expr_inc = None, None
    if not check_token(token_stream, ';'):
        expr_init = get_e(token_stream)
    next_token(token_stream, ';')
    expr_test = get_e(token_stream)
    next_token(token_stream, ';')
    if not check_token(token_stream, ')'):
        expr_inc = get_e(token_stream)
    next_token(token_stream, ')')
    stmt = get_stmt(token_stream)
    return ForStmt(expr_test, stmt, expr_init, expr_inc)

'''ReturnStmt::= return < Expr > ;'''
def get_return_stmt(token_stream):
    r = ReturnStmt()
    if check_token(token_stream, 'return'):
        r.set_position(token_stream[pos])
        tok = token_stream[pos]
        col_st, lineno = tok['col_st'], tok['lineno']
    next_token(token_stream, 'return')
    if not check_token(token_stream, ';'):
        expr = get_e(token_stream)
        ret = ReturnStmt(expr)
        col_nd, line_nd = expr.col_nd, expr.line_nd
        ret.inherit_position(col_st, col_nd, lineno, line_nd)
        next_token(token_stream, ';')
        return ret
    return r
        
'''BreakStmt::= break ;'''
def get_break_stmt(token_stream):
    b = BreakStmt()
    b.set_position(token_stream[pos])
    next_token(token_stream, 'break')
    next_token(token_stream, ';')
    return b

'''PrintStmt::= Print ( Expr+ , ) ;'''
def get_print_stmt(token_stream):
    print_stmt = PrintStmt()
    next_token(token_stream, 'Print')
    next_token(token_stream, '(')
    expr = get_e(token_stream)
    print_stmt.add(expr)
    rest_print_stmts = get_rest_print_stmts(token_stream)
    print_stmt.add_all(rest_print_stmts.exprs)
    next_token(token_stream, ')')
    next_token(token_stream, ';')
    return print_stmt

def get_rest_print_stmts(token_stream):
    global pos
    if check_token(token_stream, ','):  
        next_token(token_stream, ',')
        print_stmt = PrintStmt()
        expr = get_e(token_stream)
        print_stmt.add(expr)
        print_stmt.add_all(get_rest_print_stmts(token_stream).exprs)
        return print_stmt
    else:
        return PrintStmt()

'''LValue::= ident'''
def get_lvalue(token_stream):
    ident  = get_ident(token_stream)
    lval = LValue(ident)
    lval.inherit_position(ident.col_st, ident.col_nd, ident.lineno, ident.line_nd)
    return lval

'''Call::= ident ( Actuals )'''
def get_call(token_stream):
    ident = get_ident(token_stream)
    next_token(token_stream, '(')
    actuals = get_actuals(token_stream)
    next_token(token_stream, ')')
    return Call(ident, actuals)

'''Actuals::= Expr+ , | ε'''
def get_actuals(token_stream):
    actuals = Actuals()
    if not check_token(token_stream, ')'):
        expr = get_e(token_stream)
        actuals.add(expr)
        expr_rest = get_actuals_rest(token_stream)
        actuals.add_all(expr_rest.exprs)
        return actuals
    else:
        return Actuals()

def get_actuals_rest(token_stream):
    global pos
    if check_token(token_stream, ','):
        next_token(token_stream, ',')
        expr = get_e(token_stream)
        actuals = Actuals()
        actuals.add(expr)
        actuals.add_all(get_actuals_rest(token_stream).exprs)
        return actuals
    else:
        return Actuals()

''' Constant::= intConstant | doubleConstant | boolConstant | stringConstant | null'''
def get_constant(token_stream):
    global pos
    c_value = token_stream[pos]['value']
    c_type = get_type(token_stream)
    const = Constant(c_type, c_value)
    col_st, col_nd = c_type.col_st, c_type.col_nd
    lineno ,line_nd= c_type.lineno, c_type.line_nd
    const.inherit_position(col_st, col_nd, lineno,line_nd)
    return const

def get_type_any(token_stream):
    global pos
    if token_stream[pos]['type'] in VOID:
        v = Void()
        v.set_position(token_stream[pos])
        next_token(token_stream, token_stream[pos]['value'])
        return v
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return get_type_any(token_stream)
    else:
        return get_type(token_stream)

'''Type ::= int | double | bool | string'''
def get_type(token_stream):
    global pos
    if token_stream[pos]['type'] in ALL_TYPES or token_stream[pos]['type'] in ALL_CONSTANTS:
        t_val = token_stream[pos]['value']
        t_type = token_stream[pos]['type'][2:]
        t = Type(t_type, t_val)
        t.set_position(token_stream[pos])
        next_token(token_stream, t_val)
        return t
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return get_type(token_stream)
    else:
        raise_decaf_error(token_stream)

def get_ident(token_stream):
    global pos
    if token_stream[pos]['type'] == 'T_Identifier':
        val = token_stream[pos]['value']
        ident = EStr(val)
        ident.set_position(token_stream[pos])
        next_token(token_stream, val)
        return ident
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return get_ident(token_stream)
    else:
        raise_decaf_error(token_stream)

'''
{} means 0 or more
E  ::= LValue= E1 | E1
E1 ::= E2 {LogicalOr E2}
LogicalOr ::= ||
E2 ::= E3 {LogicalAnd E3}
LogicalAnd ::= &&
E3 ::= E4 {EqualityExpr E4}
EqualityExpr ::= == | !=
E4 ::= E5 {RelationalExpr E5}
RelationalExpr ::= < | <= | > | >=
E5 ::= E6 {ArithmaticOperator E6}
ArithmaticOperator ::= + | -
E6 ::= E7 {Prod E7}
Prod ::= *| / | %
E7 ::= <UnaryOperator> E7 | Lvalue | (E) | Constant | Call | ReadInteger() | ReadLine()
UnaryOperator ::= ! | -

'''

def get_e(token_stream):
    global pos
    lvalue = None
    op_str = None
    if check_token_type(token_stream, 'T_Identifier'):
        start = pos + 1
        while token_stream[start]['type'] in WHITE_SPACE:
            start += 1
        if token_stream[start]['value'] == '=':
            lvalue = get_lvalue(token_stream)
            op_str = EStr('=')
            op_str.set_position(token_stream[start])
            col_st, lineno = lvalue.col_st, lvalue.lineno
            next_token(token_stream, "=")
    if lvalue == None:
        tok = token_stream[pos]
        col_st, lineno = tok['col_st'], tok['lineno']
    e1 = get_e1(token_stream)
    col_nd, line_nd = e1.col_nd, e1.line_nd
   
    e = E(lvalue, e1, op_str)
    e.inherit_position(col_st, col_nd, lineno, line_nd)
    return e

def get_e1(token_stream):
    e2 = get_e2(token_stream)
    while(check_token(token_stream, '||')):
        op = token_stream[pos]['value']
        op_str = EStr(op)
        op_str.set_position(token_stream[pos])
        next_token(token_stream, op)
        e2_right = get_e2(token_stream)
        lineno, col_st = e2.lineno, op_str.col_st
        line_nd, col_nd = e2_right.line_nd, e2_right.col_nd
        e2 = EBinary(e2, op_str, "LogicalExpr: ", e2_right)
        e2.inherit_position(col_st, col_nd, lineno, line_nd)

    return e2
def get_e2(token_stream):
    e3 = get_e3(token_stream)
    while(check_token(token_stream, '&&')):
        op = token_stream[pos]['value']
        op_str = EStr(op)
        op_str.set_position(token_stream[pos])
        next_token(token_stream, op)
        e3_right = get_e3(token_stream)
        lineno, col_st = e3.lineno, op_str.col_st
        line_nd, col_nd = e3_right.line_nd, e3_right.col_nd
        e3 = EBinary(e3, op_str, "LogicalExpr: ", e3_right)
        e3.inherit_position(col_st, col_nd, lineno, line_nd)
    return e3
def get_e3(token_stream):
    e4 = get_e4(token_stream)
    while(check_token(token_stream, ['==', '!='])):
        op = token_stream[pos]['value']
        op_str = EStr(op)
        op_str.set_position(token_stream[pos])
        next_token(token_stream, op)
        e4_right = get_e4(token_stream)
        lineno, col_st = e4.lineno, op_str.col_st
        line_nd, col_nd = e4_right.line_nd, e4_right.col_nd
        e4 = EBinary(e4, op_str, "EqualityExpr: ", e4_right)
        e4.inherit_position(col_st, col_nd, lineno, line_nd)
    return e4
def get_e4(token_stream):
    e5 = get_e5(token_stream)
    while(check_token(token_stream, ['<', '<=', '>', '>='])):
        op = token_stream[pos]['value']
        op_str = EStr(op)
        op_str.set_position(token_stream[pos])
        next_token(token_stream, op)
        e5_right = get_e5(token_stream)
        lineno, col_st = e5.lineno, op_str.col_st
        line_nd, col_nd = e5_right.line_nd, e5_right.col_nd
        e5 = EBinary(e5, op_str, "RelationalExpr: ", e5_right)
        e5.inherit_position(col_st, col_nd, lineno, line_nd)
    return e5
def get_e5(token_stream):
    e6 = get_e6(token_stream)
    while(check_token(token_stream, ['+', '-'])):
        op = token_stream[pos]['value']
        op_str = EStr(op)
        op_str.set_position(token_stream[pos])
        next_token(token_stream, op)
        e6_right = get_e6(token_stream)
        lineno, col_st = e6.lineno, op_str.col_st
        line_nd, col_nd = e6_right.line_nd, e6_right.col_nd
        e6 = EBinary(e6, op_str, "ArithmeticExpr: ", e6_right)
        e6.inherit_position(col_st, col_nd, lineno, line_nd)
    return e6
    
def get_e6(token_stream):
    e7 = get_e7(token_stream)
    while(check_token(token_stream, ['*', '/', '%'])):
        op = token_stream[pos]['value']
        op_str = EStr(op)
        op_str.set_position(token_stream[pos])
        next_token(token_stream, op)
        e7_right = get_e7(token_stream)
        lineno, col_st = e7.lineno, op_str.col_st
        line_nd, col_nd = e7_right.line_nd, e7_right.col_nd
        e7 = EBinary(e7, op_str, "ArithmeticExpr: ", e7_right)
        e7.inherit_position(col_st, col_nd, lineno, line_nd)
    return e7
def get_e7(token_stream):
    global pos
    if token_stream[pos]['value'] in ['!', '-']:
        op = token_stream[pos]['value']
        op_str = EStr(op)
        op_str.set_position(token_stream[pos])
        next_token(token_stream, op)
        e7 = get_e7(token_stream)
        if op == '-':
            e7_u =  E7Unary(op_str, "ArithmeticExpr: ", e7)
        else:
            e7_u = E7Unary(op_str, "LogicalExpr: ", e7)
        col_st, col_nd = op_str.col_st, e7.col_nd
        lineno, line_nd = op_str.lineno, e7.line_nd
        e7_u.inherit_position(col_st, col_nd, lineno, line_nd)
        return e7_u
    elif token_stream[pos]['type'] in ALL_CONSTANTS:
        const = get_constant(token_stream)
        e7_member = E7Member(const)
        col_st, col_nd = const.col_st, const.col_nd
        lineno, line_nd = const.lineno, const.line_nd
        e7_member.inherit_position(col_st, col_nd, lineno, line_nd)
        return e7_member
    
    elif token_stream[pos]['type'] == 'T_Identifier':
        lvalue = get_lvalue(token_stream)
        #Function Call
        if check_token(token_stream, '('):
            next_token(token_stream, '(')
            a = get_actuals(token_stream)
            call = Call(lvalue.ident, a)
            col_st, lineno = lvalue.ident.col_st, lvalue.ident.lineno
            if check_token(token_stream, ')'):
                tok = token_stream[pos]
                col_nd, line_nd = tok['col_nd'], tok['lineno']
            next_token(token_stream, ')')
            call.inherit_position(col_st, col_nd, lineno, line_nd)
            return call
        #LValue
        else:
            e7 = E7Member(lvalue)
            l = lvalue.ident
            e7.inherit_position(l.col_st, l.col_nd, l.lineno, l.line_nd)
            return e7
    
    elif token_stream[pos]['value'] == '(':
        next_token(token_stream, '(')
        e = get_e(token_stream)
        next_token(token_stream, ')')
        e7_member = E7Member(e)
        col_st, col_nd = e.col_st, e.col_nd
        lineno, line_nd = e.lineno, e.line_nd
        e7_member.inherit_position(col_st, col_nd, lineno,line_nd)
        return e7_member
    elif token_stream[pos]['type'] in ['T_ReadInt', 'T_ReadLine']:
        k = token_stream[pos]['type']
        e7_keyword = E7Keyword(KEYWORD_EXPR[k])
        e7_keyword.set_position(token_stream[pos])
        next_token(token_stream, token_stream[pos]['value'])
        next_token(token_stream, '(')
        if check_token(token_stream, ')'):
            e7_keyword.line_nd = token_stream[pos]['lineno']
            e7_keyword.col_nd = token_stream[pos]['col_nd']
        next_token(token_stream, ')')
        return e7_keyword
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return get_e7(token_stream)
    else:
        raise_decaf_error(token_stream)

def next_token(token_stream, match_value):
    global pos
    if token_stream[pos]['value'] == match_value:
        pos += 1
        return 
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        next_token(token_stream, match_value)
    else:
        raise_decaf_error(token_stream)
    
def check_token(token_stream, match_value):
    global pos
    if isinstance(match_value, list):
        if token_stream[pos]['value'] in match_value:
            return True
        elif token_stream[pos]['type'] in WHITE_SPACE:
            pos += 1
            return check_token(token_stream, match_value)
        else:
            return False
    else:
        if token_stream[pos]['value'] == match_value:
            return True
        elif token_stream[pos]['type'] in WHITE_SPACE:
            pos += 1
            return check_token(token_stream, match_value)
        else:
            return False

def check_token_type(token_stream, match_value):
    global pos
    if token_stream[pos]['type'] == match_value:
        return True
    elif token_stream[pos]['type'] in WHITE_SPACE:
        pos += 1
        return check_token_type(token_stream, match_value)
    else:
        return False
def debug_stream(token_stream):
    global pos
    for token in token_stream[pos:]:
        print("\t", token['value'])
    print()

raw_input = '''
int main()
{
    bool i ;
	i= -i;
}
'''
def parse(raw_input):
    token_stream , input_raw = lexical_analysis(raw_input, True)
    raw_lines = [line for line in input_raw.split('\n')]
    #print(token_stream)
    try:
        program = get_program(token_stream)
        #print("GOT the program")
        #program.print_self()
        return program, raw_lines
    except DecafSyntaxError as e:
        print("*** Error line " + str(e.lineno))
        print(raw_lines[e.lineno - 1])
        print(''.join(' ' * (e.col_st-1)) + ''.join('^' * (e.col_nd - e.col_st + 1)) )
        print(e.message)
        return None, None
#parse(raw_input)