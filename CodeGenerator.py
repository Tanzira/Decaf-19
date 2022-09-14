#!/usr/bin/env python
# -*- coding: utf-8 -*- 
from __future__ import unicode_literals
from SemanticAnalyser import *
OP_INST = {'+' : 'add', '*' : 'mul', '/' : 'div',
             '-' : 'sub', '%' : 'rem', '<' : 'slt',
              '<=' : 'sle', '>' : 'sgt', '>=' : 'sge',
              '==' : 'seq', '!=' : 'sne', '!' : 'not',
              '&&' : 'and', '||' : 'or'}
instruction_stream = []
return_count = 0


class MIPSReg:
    def __init__(self):
        self.reg = []
        for r in ['t9', 'a3', 's7', 'k1']:
            c, i = r[0], int(r[1])
            for n in range(i+1):
                self.reg.append(['$' + c + str(n), True])
    def next(self):
        for r in self.reg:
            if r[1]:
                r[1] = False
                return r[0]
        print("All registers occupied")
        return None
    def free(self, r):
        for ri in self.reg:
            if r == ri[0]:
                ri[1] = True
                return
        print("invalid register")
        return
    def busy(self, r):
        for ri in self.reg:
            if r == ri[0]:
                ri[1] = False
                return
        print("invalid register")
        return

class Label:
    def __init__(self):
        self.count = -1
    def next(self):
        self.count += 1
        return "label_" + str(self.count) + ":"
    
def emit(op, r3 = '', r1 = '', r2 = '', label = False):
    pre = '' if label else '    '
    global instruction_stream
    instruction_stream.append(' '.join([pre, op, r3, r1, r2]))

class Memory:
    def __init__(self, is_global = False):
        self.loc = 8
        self.base = '$gp' if is_global else '$fp'
    def next(self):
        self.loc += 4
        return '-' + str(self.loc) + "(" + self.base + ")", self.loc
    def reset(self, is_global = False):
        self.loc = 8
        self.base = '$gp' if is_global else '$fp'
class GeneratorVisitor:
    def __init__(self):
        self.current_symbol_table = None
        self.register = MIPSReg()
        self.mem = Memory(is_global = True)
        self.label_gen = Label()
        self.hasmain = False

    def visit_program(self, program):
        self.visit_program_first_pass(program)
    # Firstpass
    def visit_program_first_pass(self, program):
        emit('.text')
        emit('.align 2')
        emit('.globl main')
        self.current_symbol_table = program.symbol_table
        for decl in program.decls:
            if isinstance(decl, VariableDecl):
                self.visit_variable_decl(decl)
            elif isinstance(decl, FunctionDecl):
                if decl.ident == 'main':
                    self.hasmain = True
                self.visit_type(decl.type_a)
                self.current_symbol_table = decl.symbol_table
                self.visit_formals(decl.formals)
                self.current_symbol_table = program.symbol_table
        self.visit_program_second_pass(program)

    def visit_program_second_pass(self, program):
        global return_count
        if not self.hasmain:
            print("*** Error.\n*** Linker: function 'main' not defined")
            return
        for decl in program.decls:
            if isinstance(decl, FunctionDecl):
                return_count = 0
                lab = decl.ident if decl.ident == 'main' else '_' + decl.ident
                emit(lab + ":", label = True)
                self.mem.reset()
                emit('subu $sp, $sp, 8')
                emit('sw $fp, 8($sp)')
                emit('sw $ra, 4($sp)')
                emit('addiu $fp, $sp, 8')
                f_entry = self.current_symbol_table.func_id_lookup(decl.ident)
                l = len(f_entry.formals.variables)
                emit('    # increasing frame size, formals: ', str(l))
                emit('subu', '$sp', '$sp', str(4*l+24))
                #emit('subu $sp, $sp, 24')
                self.current_symbol_table = decl.symbol_table
                for i in range(len(f_entry.formals.variables)):
                    var = f_entry.formals.variables[i]
                    id_entry = self.current_symbol_table.id_lookup(var.ident)
                    loc = (len(f_entry.formals.variables) - i) * 4
                    id_entry.entry['mem'] = (str(loc) + '($fp)', loc)
                self.visit_stmtblock(decl.stmtblock)
                if return_count == 0:
                    emit('move $sp, $fp')
                    emit('lw $ra, -4($fp)')
                    emit('lw $fp, 0($fp)')
                    emit('jr $ra')
    
    def get_frame_sz(self, func_decl):
        len_formals = len(func_decl.formals.variables)
        len_locals = len(func_decl.stmtblock.variable_decls)
        return 4 * (len_formals + len_locals)

    def visit_variable_decl(self, var_decl):
        self.visit_variable(var_decl.variable)

    def visit_variable(self, variable):
        self.visit_type(variable.v_type)
        id_entry = self.current_symbol_table.id_lookup(variable.ident)
        id_entry.entry['mem'] = self.mem.next()
        emit("# "+ variable.ident + " stored in " + id_entry.entry['mem'][0])

    def visit_type(self, v_type):
        pass

    def visit_formals(self, formals):
        for variable in formals.variables:
            self.visit_variable(variable)

    def visit_stmtblock(self, stmtblock):
        self.current_symbol_table = stmtblock.symbol_table
        l =  len(stmtblock.variable_decls)
        if l != 0:
            emit('    # increasing frame size, stmtblock: ', str(l))
            emit('subu', '$sp', '$sp', str(4*l))
        for variable_decl in stmtblock.variable_decls:
            self.visit_variable_decl(variable_decl)
        for stmt in stmtblock.stmts:
            self.visit_stmt(stmt)
        self.current_symbol_table = stmtblock.symbol_table.parent

    def visit_stmt(self, stmt):
        if isinstance(stmt, ExprStmt):
            if stmt.expr != None:
                self.visit_expr(stmt.expr) 
        elif isinstance(stmt, StmtBlock):
            self.visit_stmtblock(stmt)
        elif isinstance(stmt, IfStmt):
            self.visit_expr(stmt.test_expr)
            r1 = stmt.test_expr.reg
            if stmt.else_stmt == None:
                label_exit = self.label_gen.next()
                r2 = self.register.next()
                emit('li', r2, '0')
                emit('beq', r1, r2, label_exit[:-1])
                self.register.free(r1)
                self.register.free(r2)
                self.visit_stmt(stmt.then_stmt)
                emit(label_exit, label=True)
            else:
                label_else = self.label_gen.next()
                label_exit = self.label_gen.next()
                r2 = self.register.next()
                emit('li', r2, '0')
                emit('beq', r1, r2, label_else[:-1])
                self.register.free(r1)
                self.register.free(r2)
                self.visit_stmt(stmt.then_stmt)
                emit('jal', label_exit[:-1])
                emit(label_else, label=True)
                self.visit_stmt(stmt.else_stmt)
                emit(label_exit, label=True)

        elif isinstance(stmt, WhileStmt):
            self.current_symbol_table = stmt.symbol_table
            label_loop = self.label_gen.next()
            label_exit = self.label_gen.next()
            self.current_symbol_table.exit_point = label_exit
            emit(label_loop, label=True)
            self.visit_expr(stmt.test_expr)
            r1 = stmt.test_expr.reg
            r2 = self.register.next()
            emit('li', r2, '0')
            emit('beq', r1, r2, label_exit[:-1])
            self.register.free(r1)
            self.register.free(r2)
            self.visit_stmt(stmt.then_stmt)
            emit('jal', label_loop[:-1])
            emit(label_exit, label=True)
            self.current_symbol_table = stmt.symbol_table.parent
        elif isinstance(stmt, ForStmt):
            self.current_symbol_table = stmt.symbol_table
            label_loop = self.label_gen.next()
            label_exit = self.label_gen.next()
            if stmt.expr_init != None:
                self.visit_expr(stmt.expr_init)
            emit(label_loop, label=True)
            
            self.visit_expr(stmt.expr_test)
            r1 = stmt.expr_test.reg
            r2 = self.register.next()
            emit('li', r2, '0')
            emit('beq', r1, r2, label_exit[:-1])
            self.register.free(r1)
            self.register.free(r2)
            self.visit_stmt(stmt.stmt)
            if stmt.expr_inc != None:
                self.visit_expr(stmt.expr_inc)
            emit('jal', label_loop[:-1])
            emit(label_exit, label=True)
            self.current_symbol_table = stmt.symbol_table.parent
        elif isinstance(stmt, BreakStmt):
            success, exit_point = self.current_symbol_table.loop_lookup(get_exit_label = True)
            print(success, exit_point)
            emit('jal', exit_point[:-1])
            
        elif isinstance(stmt, PrintStmt):
            for i in range(len(stmt.exprs)):
                expr = stmt.exprs[i]
                self.visit_expr(expr)
                emit('subu $sp, $sp, 4')
                emit('sw', expr.reg, '4($sp)')
                t = expr.e_type.t_type
                if t == 'Int':
                    emit('jal _PrintInt')
                elif t == 'Bool':
                    emit('jal _PrintBool')
                elif t== 'String':
                    emit('jal _PrintString')
                emit('add $sp, $sp, 4')
                
        elif isinstance(stmt, ReturnStmt):
            global return_count
            return_count += 1
            if stmt.expr != None:
                
                self.visit_expr(stmt.expr)
                emit('move', '$v0', stmt.expr.reg)
                self.register.free(stmt.expr.reg)
            emit('move $sp, $fp')
            emit('lw $ra, -4($fp)')
            emit('lw $fp, 0($fp)')
            emit('jr $ra')

    def visit_expr(self, expr):
        if isinstance(expr, E7):
            self.visit_e7(expr)
        else:
            if expr.lvalue != None:
                # Expr::= LValue=Expr
                self.visit_lvalue(expr.lvalue, load = False)
                self.visit_ebinary(expr.e1)
                r1 = expr.e1.reg
                id_entry = self.current_symbol_table.id_lookup(expr.lvalue.ident)
                r2 = id_entry.entry['mem'][0]
                emit('sw', r1, r2)
                self.register.free(r1)
                expr.reg = r2
            else:
                self.visit_ebinary(expr.e1)
                if expr.e1.e_type.t_type != 'Void':
                    expr.reg = expr.e1.reg

    def visit_ebinary(self, e1):
        global OP_INST
        if isinstance(e1, EBinary):
            self.visit_ebinary(e1.e_left)
            self.visit_ebinary(e1.e_right)
            r1 = e1.e_left.reg
            r2 = e1.e_right.reg
            emit(OP_INST.get(e1.op, 'undefined'), r1, r1, r2)
            e1.reg = r1
            self.register.free(r2)
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
        #print("E7 u: ", e7_unary.e.reg) 
        self.visit_expr(e7_unary.e) 
        if e7_unary.op == '-':
            r0 = self.register.next()
            emit('li', r0, '0')
            r1 = e7_unary.e.reg
            emit('sub', r1, r0, r1)
            self.register.free(r0)
            e7_unary.reg = r1
        elif e7_unary.op == '!':
            label_else = self.label_gen.next()
            label_end = self.label_gen.next()
            r = e7_unary.e.reg
            r0 = self.register.next()
            r1 = self.register.next()
            emit('li', r0, '0')
            emit('li', r1, '1')
            #if 1 go to else
            emit('bne', r, r0, label_else[:-1])
            emit('move', r, r1)
            emit('jal', label_end[:-1])
            emit(label_else, label=True)
            emit('move', r, r0)
            emit(label_end, label=True)
            self.register.free(r0)
            self.register.free(r1)
            e7_unary.reg = r

    def visit_e7_keyword(self, l_func):
        if l_func.k == KEYWORD_EXPR['T_ReadLine']:
            emit('jal _ReadLine')
        elif l_func.k == KEYWORD_EXPR['T_ReadInt']:
            emit('jal _ReadInteger')
        r1 = self.register.next()
        emit('move', r1, '$v0')
        l_func.reg = r1
    def visit_e7_member(self, e7):
        if isinstance(e7.member, Constant):
            self.visit_const(e7.member)
        elif isinstance(e7.member, LValue):
            self.visit_lvalue(e7.member)
        elif isinstance(e7.member, E):
            self.visit_expr(e7.member)
        e7.reg = e7.member.reg
    def visit_call(self, e7):
        saved_reg = []
        emit("    # saving registers")
        for r in self.register.reg:
            if not r[1]:
                mem_loc = self.mem.next()
                emit('sw', r[0], mem_loc[0])
                saved_reg.append((r[0], mem_loc))
                self.register.free(r[0])
        emit('    # done saving')
        actuals = e7.actuals
        for e in actuals.exprs:
            self.visit_expr(e)
            emit('subu $sp, $sp, 4')
            emit('sw', e.reg, '4($sp)')
            self.register.free(e.reg)
        emit('jal', '_' + e7.ident)
        emit('    # reloading registers')
        for r in saved_reg:
            emit('lw', r[0], r[1][0])
            self.register.busy(r[0])
        emit('    # done reloading')
        if e7.e_type.t_type != 'Void':
            r = self.register.next()
            emit('move', r, '$v0')
            e7.reg = r
    def visit_const(self, const):
        var_type = const.c_type.t_type
        if var_type == 'StringConstant':
            str_lab = self.label_gen.next()
            emit('.data')
            emit(str_lab, '.asciiz', str(const.c_value))
            emit('.text')
            r1 = self.register.next()
            emit("la", r1, str_lab[:-1])
            const.reg = r1
        elif var_type == 'IntConstant':
            r1 = self.register.next()
            emit("li", r1, str(const.c_value))
            const.reg = r1
        else:
            bool_val = 1 if const.c_value == 'true' else 0
            r1 = self.register.next()
            emit("li", r1, str(bool_val))
            const.reg = r1
        
    def visit_lvalue(self, lvalue, load=True):
        if load:
            id_entry = self.current_symbol_table.id_lookup(lvalue.ident)
            r1 = self.register.next()
            emit('lw', r1, id_entry.entry['mem'][0])
            lvalue.reg = r1


raw_input = '''

    int a;
    int b;

void f(){
    Print(a);
}
void main() {
	int c;
    a = 5;
	f();
}

'''
def __main__():
    global instruction_stream
    FLAG, program = semantic_analyser(raw_input)
    #print(raw_input)
    #program.print_self()
    if FLAG == True:
        generator = GeneratorVisitor()
        generator.visit_program_first_pass(program)
        if generator.hasmain:
            for line in instruction_stream:
                print(line)
            with open('program.s', 'w') as out:
                out.write('\n'.join(instruction_stream))
                out.write('\n')
    else:
        print("None!")

__main__()
