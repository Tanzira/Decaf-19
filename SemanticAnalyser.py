#!/usr/bin/env python
# -*- coding: utf-8 -*- 
from __future__ import unicode_literals
from ASTGenerator import *

REPL_CONST = {'StringConstant' : ('String', 'string'), 'BoolConstant' : ('Bool', 'bool') , \
    'DoubleConstant' : ('Double', 'double'),'IntConstant' : ('Int', 'int'), 'Null' : ('Null', 'null')}
st_builder = None
return_count = 0
raw_lines = []
FLAG = True
class IDEntry:
    def __init__(self, id, id_type):
        self.entry = {}
        self.entry['id'] = id
        self.entry['type'] = id_type

class FuncIDEntry(IDEntry):
    def __init__(self, id, id_type, formals):
        super().__init__(id, id_type)
        self.formals = formals

class SymbolTable:
    def __init__(self, parent, label = 'block', func_id = None):
        self.parent = parent
        self.table = {}
        self.label = label
        self.func_id = func_id
        self.exit_point = None
    def install(self, id, id_type, formals = None):
        if id in self.table:
            #print("*** Function '" + id + "' already declared before.")
            return False
        else:
            if formals == None:
                id_entry = IDEntry(id,id_type) 
                self.table[id] = id_entry
            else:
                func_entry = FuncIDEntry(id, id_type, formals)
                self.table[id] = func_entry
            return True
    def id_lookup(self, id):
        id_entry = self.table.get(id, None)
        if id_entry != None and not isinstance(id_entry, FuncIDEntry):
            return id_entry
        elif id_entry == None and self.parent != None:
            return self.parent.id_lookup(id)
        else:
            return None
    def func_id_lookup(self, id):
        func_id_entry = self.table.get(id, None)
        if func_id_entry != None:
            return func_id_entry
        elif func_id_entry == None and self.parent != None:
            return self.parent.func_id_lookup(id)
        else:
            #print("*** No declaration found for function '" + id + "'")
            return None

    def loop_lookup(self, get_exit_label = False):
        print(get_exit_label)
        if self.label == 'loopBlock':
            if get_exit_label:
                return True, self.exit_point
            return True
        elif self.parent == None:
            return False
        else:
            return self.parent.loop_lookup(get_exit_label = get_exit_label)


    def return_lookup(self, e):
        pass
    def func_lookup(self):
        if self.label == 'funcBlock':
            return self.func_id
        elif self.parent == None:
            return None
        else:
            return self.parent.func_lookup()

class SymbolTableBuilder:
    def __init__(self):
        self.level = 0
        self.symbol_table = None
    def initialize_scope(self, label = 'block', func_id = None):
        next_symbol_table = SymbolTable(self.symbol_table, label, func_id)
        self.level += 1
        self.symbol_table = next_symbol_table
    def expand_scope(self, label = 'block'):
        pass
    def finalize_scope(self):
        if self.level > 0:
            self.level -= 1
            current_table = self.symbol_table
            self.symbol_table = self.symbol_table.parent
            return current_table
        else:
            print("Invalid access in symbol table builder")
    def install(self, id, id_type, formals = None):
        return self.symbol_table.install(id, id_type, formals)

    def id_lookup(self, id):
        return self.symbol_table.id_lookup(id)

    def call_lookup(self, id, actuals):
        self.symbol_table.call_lookup(id, actuals)
    def loop_lookup(self):
        return self.symbol_table.loop_lookup()
    def return_lookup(self, e):
        return self.symbol_table.return_lookup()
    def func_lookup(self):
        return self.symbol_table.func_lookup()
    def func_id_lookup(self, id):
        return self.symbol_table.func_id_lookup(id)

class GhostType(ASTNode):
    def __init__(self):
        self.t_type = 'Ghost'
        self.t_val = 'ghost'

class Visitor:
    def visit_program(self, program):
        self.visit_program_first_pass(program)
    # Firstpass
    def visit_program_first_pass(self, program):
        global st_builder
        st_builder.initialize_scope()
        for decl in program.decls:
            if isinstance(decl, VariableDecl):
                self.visit_variable_decl(decl)
            elif isinstance(decl, FunctionDecl):
                ident = decl.ident
                self.visit_type(decl.type_a)
                success = st_builder.install(ident, decl.type_a, decl.formals)
                if not success:
                    msg = "*** '" + decl.ident + "' already declared"
                    self.mark(decl.ident, msg)
                    decl.symbol_table = None
                    continue
                st_builder.initialize_scope(label = 'funcBlock', func_id = decl.ident)
                self.visit_formals(decl.formals)
                decl.symbol_table = st_builder.finalize_scope()
        program.symbol_table = st_builder.finalize_scope()
        self.visit_program_second_pass(program)

    def visit_program_second_pass(self, program):
        global st_builder, return_count
        for decl in program.decls:
            if isinstance(decl, FunctionDecl) and decl.symbol_table != None:
                return_count = 0
                st_builder.symbol_table = decl.symbol_table
                st_builder.level += 2
                self.visit_stmtblock(decl.stmtblock)
                if return_count == 0 and decl.type_a.t_type != 'Void':
                    msg = "*** Incompatible return: void given, "\
                    + decl.type_a.t_val + " expected"
                    self.mark(decl.type_a, msg)

    def visit_variable_decl(self, var_decl):
        self.visit_variable(var_decl.variable)

    def visit_variable(self, variable):
        self.visit_type(variable.v_type)
        self.visit_ident(variable.ident)
        success = st_builder.install(variable.ident, variable.v_type)
        if not success:
            msg = "*** '" + variable.ident + "' already declared"
            self.mark(variable.ident, msg)

    def visit_type(self, v_type):
        pass
    def visit_ident(self, ident):
        pass

    def visit_formals(self, formals):
        for variable in formals.variables:
            self.visit_variable(variable)

    def visit_stmtblock(self, stmtblock):
        global st_builder
        st_builder.initialize_scope()
        for variable_decl in stmtblock.variable_decls:
            self.visit_variable_decl(variable_decl)
        for stmt in stmtblock.stmts:
            self.visit_stmt(stmt)
        st = st_builder.finalize_scope()
        stmtblock.symbol_table = st
        
    def visit_stmt(self, stmt):
        global st_builder
        if isinstance(stmt, ExprStmt):
            if stmt.expr != None:
                self.visit_expr(stmt.expr) 
        elif isinstance(stmt, StmtBlock):
            self.visit_stmtblock(stmt)
        elif isinstance(stmt, IfStmt):
            self.visit_expr(stmt.test_expr)
            if stmt.test_expr.e_type.t_type != 'Bool'and stmt.test_expr.e_type.t_type != 'Ghost':
                msg = "*** Test expression must have boolean type"
                self.mark(stmt.test_expr, msg)
            self.visit_stmt(stmt.then_stmt)
            if stmt.else_stmt != None:
                self.visit_stmt(stmt.else_stmt)
        elif isinstance(stmt, WhileStmt):
            st_builder.initialize_scope(label='loopBlock')
            self.visit_expr(stmt.test_expr)
            if stmt.test_expr.e_type.t_type != 'Bool'and stmt.test_expr.e_type.t_type != 'Ghost':
                msg = "*** Test expression must have boolean type"
                self.mark(stmt.test_expr, msg)
            self.visit_stmt(stmt.then_stmt)
            stmt.symbol_table = st_builder.finalize_scope()
        elif isinstance(stmt, ForStmt):
            st_builder.initialize_scope(label='loopBlock')
            if stmt.expr_init != None:
                self.visit_expr(stmt.expr_init)
            self.visit_expr(stmt.expr_test)
            if stmt.expr_test.e_type.t_type != 'Bool' and stmt.expr_test.e_type.t_type != 'Ghost' :
                msg = "*** Test expression must have boolean type"
                self.mark(stmt.expr_test, msg)
            if stmt.expr_inc != None:
                self.visit_expr(stmt.expr_init)
            self.visit_stmt(stmt.stmt)
            stmt.symbol_table = st_builder.finalize_scope()
        elif isinstance(stmt, BreakStmt):
            if not st_builder.loop_lookup():
                msg = "*** break is only allowed inside a loop"
                self.mark(stmt, msg)
        elif isinstance(stmt, PrintStmt):
            for i in range(len(stmt.exprs)):
                expr = stmt.exprs[i]
                self.visit_expr(expr)
                success, result = self.match_type(['String', 'Int', 'Bool'], expr.e_type)
                if not success:
                    msg = "*** Incompatible argument " + str(i+1) + " : "+ expr.e_type.t_val+\
                         " given, int/bool/string expected"
                    self.mark(expr, msg)
            stmt.e_type = Void()

        elif isinstance(stmt, ReturnStmt):
            global return_count
            return_count += 1
            func_id = st_builder.func_lookup()
            if func_id == None:
                msg = "*** Return is only allowed inside a function"
                self.mark(stmt, msg)
            else:
                func_id_entry = st_builder.func_id_lookup(func_id)
                if stmt.expr != None:
                    self.visit_expr(stmt.expr)
                    stmt.e_type = stmt.expr.e_type
                    if func_id_entry.entry['type'].t_type != stmt.e_type.t_type:
                        msg = "*** Incompatible return: " + stmt.e_type.t_val + " given, "\
                             + func_id_entry.entry['type'].t_val + " expected"
                        self.mark(stmt, msg)
                else:
                    #print("YESSSSSS")
                    if func_id_entry.entry['type'].t_type != 'Void':
                        msg = "*** Incompatible return: void given, "\
                             + func_id_entry.entry['type'].t_val + " expected"
                        self.mark(stmt, msg)
                    else:
                        stmt.e_type = Void()

    def visit_expr(self, expr):
        if isinstance(expr, E7):
            self.visit_e7(expr)
        else:
            if expr.lvalue != None:
                self.visit_lvalue(expr.lvalue)
                self.visit_ebinary(expr.e1)
                l_type = expr.lvalue.e_type
                eb_type = expr.e1.e_type
                op = expr.op_str
                if l_type.t_type == eb_type.t_type or eb_type.t_type == 'Ghost':
                    expr.e_type = eb_type
                else:
                    expr.e_type = GhostType()
                    msg = "*** Incompatible operands: " + l_type.t_val  + ' = ' + eb_type.t_val
                    self.mark(op, msg)
            else:
                self.visit_ebinary(expr.e1)
                eb_type = expr.e1.e_type
                expr.e_type = eb_type

    def visit_ebinary(self, e1):
        if isinstance(e1, EBinary):
            if e1.e_right != None and e1.e_left != None:
                self.visit_ebinary(e1.e_left)
                self.visit_ebinary(e1.e_right)
                p = e1.e_left.e_type
                q = e1.e_right.e_type
                op = e1.op
                if op in OP_ARITHMETIC:
                    success, result_type = self.match_type(['Int', 'Double'], p, q)
                elif op in OP_RELATIONAL:
                    success, result_type = self.match_type(['Int', 'Double'], p, q)
                    if result_type.t_type != 'Ghost' :
                        result_type = Type('Bool', 'bool')
                elif op in OP_LOGICAL:
                    success, result_type = self.match_type(['Bool'], p, q)
                if not success :
                    msg = "*** Incompatible operands: " + p.t_val + ' ' + op + ' ' + q.t_val
                    self.mark(op, msg)
                e1.e_type = result_type
            else:
                self.visit_ebinary(e1.e_left)
                e1.e_type = e1.e_left.e_type
        elif isinstance(e1, E7):
            self.visit_e7(e1)
    def visit_e7(self, e7):
        if isinstance(e7, E7Unary):
            self.visit_e7_unary(e7)
        elif isinstance(e7, E7Keyword):
            self.visit_e7_keyword(e7)
        elif isinstance(e7, E7Member):
            self.visit_e7_member(e7)
        elif isinstance(e7, Call):
            self.visit_call(e7)
    def visit_e7_unary(self, e7_unary):
        self.visit_expr(e7_unary.e)
        #Type checking starts
        e_type = e7_unary.e.e_type
        if e7_unary.op == '-':
            success, result_type = self.match_type(['Int', 'Double'], e_type)
        elif e7_unary.op == '!':
            success, result_type = self.match_type(['Bool'], e_type)
        if not success:
            msg = "*** Incompatible operands: " + e7_unary.op + ' ' + e_type.t_val
            self.mark(e7_unary.op, msg)
        e7_unary.e_type = result_type

    def visit_e7_keyword(self, l_func):
        if l_func.k == KEYWORD_EXPR['T_ReadLine']:
            l_func.e_type = Type("String", 'string')
        elif l_func.k == KEYWORD_EXPR['T_ReadInt']:
            l_func.e_type = Type("Int", 'int')
    def visit_e7_member(self, e7):
        global st_builder
        if isinstance(e7.member, Constant):
            self.visit_const(e7.member)
            e7.e_type = e7.member.e_type
        elif isinstance(e7.member, LValue):
            self.visit_lvalue(e7.member)
        elif isinstance(e7.member, E):
            self.visit_expr(e7.member)
        e7.e_type = e7.member.e_type
    def visit_call(self, e7):
        func_id_entry = st_builder.func_id_lookup(e7.ident)
        
        if func_id_entry == None:
            msg = "*** No declaration found for function '"+ e7.ident + "'"
            self.mark(e7.ident, msg)
            e7.e_type = GhostType()
        else:
            if not isinstance(func_id_entry, FuncIDEntry):
                msg = "*** Variable '"+ e7.ident + "' not callable"
                self.mark(e7.ident, msg)
                e7.e_type = GhostType()
                
            else:
                formals = func_id_entry.formals.variables
                actuals = e7.actuals.exprs
                if len(formals) != len(actuals):
                    msg = "*** Function '" + func_id_entry.entry['id'] +\
                        "' expects "+ str(len(formals)) + " arguments but " + str(len(actuals)) +" given"
                    self.mark(e7.ident, msg)
                else:
                    pairs = list(zip(actuals, formals))
                    for i in range(len(pairs)):
                        p, q = pairs[i]
                        self.visit_expr(p)
                        if p.e_type.t_type != q.v_type.t_type:
                            msg = "*** Incompatible argument " + str(i+ 1) + ": " +\
                                p.e_type.t_val + " given, " +q.v_type.t_val + " expected"
                            self.mark(p, msg)
                e7.e_type = func_id_entry.entry['type']
    def visit_const(self, const):
        self.visit_type(const.c_type)
        c_type_val = REPL_CONST.get(const.c_type.t_type, None)
        const.e_type = Type(c_type_val[0], c_type_val[1])
    def visit_lvalue(self, lvalue):
        self.visit_ident(lvalue.ident)
        id_entry = st_builder.id_lookup(lvalue.ident)
        if id_entry != None:
            lvalue.e_type = id_entry.entry['type']
        else:
            msg = "*** No declaration found for variable '" + lvalue.ident + "'"
            self.mark(lvalue.ident, msg)
            lvalue.e_type = GhostType()
    def mark(self, ast_node, msg):
        global FLAG
        FLAG = False
        #print(ast_node.col_st, ast_node.col_nd, ast_node.lineno, ast_node.line_nd)
        global raw_lines
        line_nd, line_st = ast_node.line_nd, ast_node.lineno
        col_st, col_nd = ast_node.col_st, ast_node.col_nd
        print("*** Error line " + str(line_nd))
        if line_nd <= line_st:
            #single line error
            print(raw_lines[line_st - 1])
            print(''.join(' ' * (col_st-1)) + ''.join('^' * (col_nd - col_st + 1)) )
        else:
            for i in range(line_st, line_nd + 1):
                print(raw_lines[i - 1])
                if i == line_st:
                    print(''.join(' ' * (col_st-1)) + ''.join('^' * (len(raw_lines[i-1]) - col_st + 1)))
                elif i == line_nd:
                    print(''.join('^' * col_nd))
                else:
                    print(''.join('^' * len(raw_lines[i-1])) )
        print(msg + '\n\n')
    def match_type(self, valid, p, q = None):
        if q == None:
            
            if p.t_type in valid + ['Ghost']:
                return True, p
            else:
                return False, GhostType()
        else:
            #both ghost type
            if isinstance(p, GhostType) and isinstance(q, GhostType):
                return True, p
            #p ghost type
            elif isinstance(p, GhostType):
                return True, q
             #q ghost type
            elif isinstance(q, GhostType):
                return True, p
                #None ghost type
            else:

                if p.t_type == q.t_type and p.t_type in valid and q.t_type in valid:
                    return True, p
                else:
                    return False, GhostType()
    

raw_input = '''
int main(){
Print(3);

}


'''
def semantic_analyser(raw_input):
    global FLAG
    global raw_lines
    program, raw_lines = parse(raw_input)
    #program.print_self()
    global st_builder
    st_builder = SymbolTableBuilder()
    visitor = Visitor()
    if program != None:
        visitor.visit_program_first_pass(program)
    return FLAG, program


