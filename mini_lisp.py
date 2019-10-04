import ply.lex as lex
import ply.yacc as yacc
import re

reserved = {
    'if': 'if',
    'print-num': 'print_num',
    'print-bool': 'print_bool',
    'and': 'and',
    'or': 'or',
    'not': 'not',
    'define': 'define',
    'lambda': 'lambda'
}
tokens = ['number', 'id', 'boolval', 'mod'] + list(reserved.values())
literals = ['+', '-', '*', '/', '>', '<', '=', '(', ')']
data_plus = []
data_mul = []
data_equ = []
data_and = []
data_or = []
define_var = {}
# lam_define = {}     # lambda的變數(id)對應到的運算式(body)
id_list = []
lam_var_list = []   # lambda裡面的參數定義
lam_id_list = []    # id that define lambda function
lam_flag = 0        # 判斷現在是否在lambda括號中
lam_body = []       # lambda的運算式
param = []          # lambda的參數(數字)
lam_var = {}        # key為exp(body)，值為id
param_pos = {}      # key為exp，值為此function的body的變數位置
pos_count = 0
param_list = []
lam_exp_record = ''
lam_var_record = []
def is_number(s):
    num = re.compile(r'0|[1-9][0-9]*|-[1-9][0-9]*')
    if num.match(s):
        return True
    else:
        return False
def is_id(s):
    if s in define_var.keys():
        return True
    else:
        return False
def is_bool(s):
    if s == '#t' or s == '#f':
        return True
    else:
        return False
    # id = re.compile(r'[a-z][a-z0-9-]*')
    # if id.match(s):
    #     return True
    # else:
    #     return False
def t_boolval(t):
    r'\#t|\#f'
    return t
def t_mod(t):
    r'mod'
    return t

def t_number(t):
    r'0|[1-9][0-9]*|-[1-9][0-9]*'
    return t  # 最後必須返回t，如果不返回，這個token就會被丢棄掉


def t_id(t):
    r'[a-zA-Z][a-z0-9-]*'
    global lam_flag
    if t.value == 'lambda':
        lam_flag = 1
    t.type = reserved.get(t.value, 'id')
    # print("id")
    return t


# 出錯處理
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)
# 不做處理的符號
t_ignore = ' \t\n\r'


def p_PROGRAM(p):
    'PROGRAM : STMTs'
    p[0] = p[1]
def p_STMTs(p):
    ''' STMTs   :  STMTs STMT
                        | STMT
        '''
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = p[2]
def p_STMT(p):
    ''' STMT    : EXP
                        | DEF_STMT
                        | PRINT_STMT
    '''
    p[0] = p[1]
def p_PRINT_STMT(p):
    ''' PRINT_STMT  : '(' print_num  EXP ')'
                                  | '(' print_bool EXP ')'
    '''

    if is_id(p[3]):
        print(define_var[p[3]])
    else:
        print(p[3])
    p[0] = p[3]
def p_EXP(p):
    ''' EXP   : boolval
                    | number
                    | VARIABLE
                    | NUM_OP
                    | LOGICAL_OP
                    | IF_EXP
                    | FUN_EXP
                    | FUN_CALL
    '''
    p[0] = str(p[1])


def p_NUM_OP(p):
    ''' NUM_OP   : PLUS
                            | MINUS
                            | MULTIPLY
                            | DIVIDE
                            | MODULUS
                            | GREATER
                            | SMALLER
                            | EQUAL
    '''
    p[0] = p[1]
def p_EXPs_p(p):
    ''' EXPs_p : EXPs_p EXP
                    | EXP
    '''
    # print('len:', len(p))
    if len(p) == 3:
        # print(p[2])
        if is_bool(p[2]):
            print('Type Error: Expect ‘number’ but got ‘boolean’.')
            exit()
        data_plus.append(p[2])
    else:
        # print(p[1])
        if is_bool(p[1]):
            print('Type Error: Expect ‘number’ but got ‘boolean’.')
            exit()
        data_plus.append(p[1])
def p_EXPs_m(p):
    ''' EXPs_m : EXPs_m EXP
                    | EXP
    '''
    if len(p) == 3:
        if is_bool(p[2]):
            print('Type Error: Expect ‘number’ but got ‘boolean’.')
            exit()
        data_mul.append(p[2])
    else:
        if is_bool(p[1]):
            print('Type Error: Expect ‘number’ but got ‘boolean’.')
            exit()
        data_mul.append(p[1])
def p_EXPs_e(p):
    ''' EXPs_e : EXPs_e EXP
                    | EXP
    '''
    if len(p) == 3:
        if is_bool(p[2]):
            print('Type Error: Expect ‘number’ but got ‘boolean’.')
            exit()
        data_equ.append(p[2])
    else:
        if is_bool(p[1]):
            print('Type Error: Expect ‘number’ but got ‘boolean’.')
            exit()
        data_equ.append(p[1])
def p_EXPs_a(p):
    ''' EXPs_a : EXPs_a EXP
                    | EXP
    '''
    if len(p) == 3:
        data_and.append(p[2])
    else:
        data_and.append(p[1])
def p_EXPs_o(p):
    ''' EXPs_o : EXPs_o EXP
                    | EXP
    '''
    if len(p) == 3:
        data_or.append(p[2])
    else:
        data_or.append(p[1])
def p_PLUS(p):
    'PLUS : "(" "+" wait EXP wait_one EXPs_p ")"'
    global pos_count
    if is_bool(p[4]):
        print('Type Error: Expect ‘number’ but got ‘boolean’.')
        exit()
    if lam_flag == 1:
        for j in range(len(data_plus)):
            if data_plus[j] != 'None':      # 因為若EXP中有其他OP，會回傳None
                if data_plus[j] in lam_var_record:      # 若data_plus[j]為function會使用到的參數
                    var_pos = data_plus[j] + ' ' + str(pos_count)   # 記錄此參數的位置 -> name pos，以便之後取代
                    param_list.append(var_pos)
                lam_body.append(data_plus[j])
                pos_count += len(data_plus[j]) + 1
        lam_body.append(p[7])
        pos_count += 2
        data_plus.clear()
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    p[0] = int(p[4])
    for i in range(len(data_plus)):
        # print(data_plus[i])
        if is_id(data_plus[i]):
            data_plus[i] = define_var[data_plus[i]]
        p[0] += int(data_plus[i])
    data_plus.clear()
def p_MINUS(p):
    ''' MINUS : '(' '-' wait EXP wait_one EXP  ')' '''
    global pos_count
    if is_bool(p[4]) or is_bool(p[6]):
        print('Type Error: Expect ‘number’ but got ‘boolean’.')
        exit()
    if lam_flag == 1:
        lam_body.append(p[6])
        if p[6] != 'None':
            if p[6] in lam_var_record:
                var_pos = p[6] + ' ' + str(pos_count)
                param_list.append(var_pos)
            pos_count += len(p[6]) + 1
        lam_body.append(p[7])
        pos_count += 2
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    if is_id(p[6]):
        p[6] = define_var[p[6]]
    p[0] = int(p[4]) - int(p[6])
def p_MULTIPLY(p):
    ''' MULTIPLY : '(' '*' wait EXP wait_one EXPs_m  ')' '''
    global pos_count
    if is_bool(p[4]):
        print('Type Error: Expect ‘number’ but got ‘boolean’.')
        exit()
    if lam_flag == 1:
        for j in range(len(data_mul)):
            if data_mul[j] != 'None':
                if data_mul[j] in lam_var_record:
                    var_pos = data_mul[j] + ' ' + str(pos_count)
                    param_list.append(var_pos)
                pos_count += len(data_mul[j]) + 1
                lam_body.append(data_mul[j])
        lam_body.append(p[7])
        pos_count += 2
        data_mul.clear()
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    p[0] = int(p[4])
    for i in range(len(data_mul)):
        if is_id(data_mul[i]):
            data_mul[i] = define_var[data_mul[i]]
        p[0] *= int(data_mul[i])
    data_mul.clear()
def p_DIVIDE(p):
    ''' DIVIDE : '(' '/' wait EXP wait_one EXP  ')' '''
    global pos_count
    if is_bool(p[4]) or is_bool(p[6]):
        print('Type Error: Expect ‘number’ but got ‘boolean’.')
        exit()
    if lam_flag == 1:
        lam_body.append(p[6])
        if p[6] != 'None':
            if p[6] in lam_var_record:
                var_pos = p[6] + ' ' + str(pos_count)
                param_list.append(var_pos)
            pos_count += len(p[6]) + 1
        lam_body.append(p[7])
        pos_count += 2
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    if is_id(p[6]):
        p[6] = define_var[p[6]]
    p[0] = int(int(p[4]) / int(p[6]))
def p_MODULUS(p):
    ''' MODULUS : '(' mod wait EXP wait_one EXP  ')' '''
    global pos_count
    if is_bool(p[4]) or is_bool(p[6]):
        print('Type Error: Expect ‘number’ but got ‘boolean’.')
        exit()
    if lam_flag == 1:
        lam_body.append(p[6])
        if p[6] != 'None':
            if p[6] in lam_var_record:
                var_pos = p[6] + ' ' + str(pos_count)
                param_list.append(var_pos)
            pos_count += len(p[6]) + 1
        lam_body.append(p[7])
        pos_count += 2
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    if is_id(p[6]):
        p[6] = define_var[p[6]]
    p[0] = int(p[4]) % int(p[6])
def p_GREATER(p):
    ''' GREATER : '(' '>' wait EXP wait_one EXP  ')' '''
    global pos_count
    if is_bool(p[4]) or is_bool(p[6]):
        print('Type Error: Expect ‘number’ but got ‘boolean’.')
        exit()
    if lam_flag == 1:
        lam_body.append(p[6])
        if p[6] != 'None':
            if p[6] in lam_var_record:
                var_pos = p[6] + ' ' + str(pos_count)
                param_list.append(var_pos)
            pos_count += len(p[6]) + 1
        lam_body.append(p[7])
        pos_count += 2
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    if is_id(p[6]):
        p[6] = define_var[p[6]]
    if int(p[4]) > int(p[6]):
        p[0] = '#t'
    else:
        p[0] = '#f'
def p_SMALLER(p):
    ''' SMALLER : '(' '<' wait EXP wait_one EXP  ')' '''
    global pos_count
    if is_bool(p[4]) or is_bool(p[6]):
        print('Type Error: Expect ‘number’ but got ‘boolean’.')
        exit()
    if lam_flag == 1:
        lam_body.append(p[6])
        if p[6] != 'None':
            if p[6] in lam_var_record:
                var_pos = p[6] + ' ' + str(pos_count)
                param_list.append(var_pos)
            pos_count += len(p[6]) + 1
        lam_body.append(p[7])
        pos_count += 2
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    if is_id(p[6]):
        p[6] = define_var[p[6]]
    if int(p[4]) < int(p[6]):
        p[0] = '#t'
    else:
        p[0] = '#f'
def p_EQUAL(p):
    ''' EQUAL : '(' '=' wait EXP wait_one EXPs_e  ')' '''
    global pos_count
    if is_bool(p[4]):
        print('Type Error: Expect ‘number’ but got ‘boolean’.')
        exit()
    if lam_flag == 1:
        for j in range(len(data_equ)):
            if data_equ[j] != 'None':
                lam_body.append(data_equ[j])
                if data_equ[j] in lam_var_record:
                    var_pos = data_equ[j] + ' ' + str(pos_count)
                    param_list.append(var_pos)
                pos_count += len(data_equ[j]) + 1
        lam_body.append(p[7])
        pos_count += 2
        data_equ.clear()
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    for i in range(len(data_equ)):
        if is_id(data_equ[i]):
            data_equ[i] = define_var[data_equ[i]]
        if str(p[4]) != str(data_equ[i]):
            p[0] = '#f'
            data_equ.clear()
            return
    data_equ.clear()
    p[0] = '#t'


def p_LOGICAL_OP(p):
    ''' LOGICAL_OP : AND_OP
                                | OR_OP
                                | NOT_OP
    '''
    p[0] = p[1]
def p_AND_OP(p):
    ''' AND_OP : '(' and wait EXP wait_one EXPs_a ')' '''
    global pos_count
    if lam_flag == 1:
        for j in range(len(data_and)):
            if data_and[j] != 'None':
                lam_body.append(data_and[j])
                if data_and[j] in lam_var_record:
                    var_pos = data_and[j] + ' ' + str(pos_count)
                    param_list.append(var_pos)
                pos_count += len(data_and[j]) + 1
        lam_body.append(p[7])
        pos_count += 2
        data_and.clear()
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    if not is_bool(p[4]):
        print('Type Error: Expect ‘boolean’.')
        exit()
    if p[4] == '#f':
        p[0] = '#f'
        return
    for i in range(len(data_and)):
        if is_id(data_and[i]):
            data_and[i] = define_var[data_and[i]]
        if not is_bool(data_and[i]):
            print('Type Error: Expect ‘boolean’.')
            exit()
        if data_and[i] != '#t':
            p[0] = '#f'
            data_and.clear()
            return
    data_and.clear()
    p[0] = '#t'
def p_OR_OP(p):
    ''' OR_OP : '(' or wait EXP wait_one EXPs_o ')' '''
    global pos_count
    if lam_flag == 1:
        for j in range(len(data_or)):
            if data_or[j] != 'None':
                lam_body.append(data_or[j])
                if data_or[j] in lam_var_record:
                    var_pos = data_or[j] + ' ' + str(pos_count)
                    param_list.append(var_pos)
                pos_count += len(data_or[j]) + 1
        lam_body.append(p[7])
        data_or.clear()
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    if not is_bool(p[4]):
        print('Type Error: Expect ‘boolean’.')
        exit()
    if p[4] == '#t':
        p[0] = '#t'
        return
    for i in range(len(data_or)):
        if is_id(data_or[i]):
            data_or[i] = define_var[data_or[i]]
        if not is_bool(data_or[i]):
            print('Type Error: Expect ‘boolean’.')
            exit()
        if data_or[i] == '#t':
            p[0] = '#t'
            data_or.clear()
            return
    data_or.clear()
    p[0] = '#f'
def p_NOT_OP(p):
    ''' NOT_OP : '(' not wait EXP wait_one ')' '''
    global pos_count
    if lam_flag == 1:
        lam_body.append(p[6])
        pos_count += 2
        return
    if is_id(p[4]):
        p[4] = define_var[p[4]]
    if not is_bool(p[4]):
        print('Type Error: Expect ‘boolean’.')
        exit()
    if p[4] == '#t':
        p[0] = '#f'
    else:
        p[0] = '#t'
def p_DEF_STMT(p):
    ''' DEF_STMT : '(' define VARIABLE EXP ')' '''
    # if p[4] == 'null':
    define_var[p[3]] = p[4]
    # print(define_var)
    p[0] = 'def'
def p_VARIABLE(p):
    'VARIABLE : id'
    p[0] = p[1]

def p_IF_EXP(p):
    ''' IF_EXP : '(' if wait TEST_EXP wait_one THAN_EXP wait_one ELSE_EXP ')'
    '''
    global pos_count
    if lam_flag == 1:
        lam_body.append(p[8])
        if p[8] != 'None':
            if p[8] in lam_var_record:
                var_pos = p[8] + ' ' + str(pos_count)
                param_list.append(var_pos)
            pos_count += len(p[8]) + 1
        lam_body.append(p[9])
        pos_count += 2
        return
    if not is_bool(p[4]):
        print('Type Error: Expect ‘boolean’.')
        exit()
    if p[4] == '#t':
        p[0] = p[6]
    else:
        p[0] = p[8]
def p_TEST_EXP(p):
    ''' TEST_EXP : EXP
    '''
    p[0] = p[1]
def p_THAN_EXP(p):
    ''' THAN_EXP : EXP
    '''
    p[0] = p[1]
def p_ELSE_EXP(p):
    ''' ELSE_EXP : EXP
    '''
    if p[-4] == '#t':
        return
    p[0] = p[1]
def p_FUN_EXP(p):
    ''' FUN_EXP : '(' lambda FUN_IDs FUN_BODY ')'
    '''
    global lam_flag, pos_count, lam_exp_record
    # print(lam_body)
    if p[3] == 'null':
        p[0] = p[4]
        lam_flag = 0
        lam_body.clear()
        return
    exp = ''
    # print(lam_body)
    for i in range(len(lam_body)):
        if lam_body[i] != 'None':
            exp = exp + lam_body[i] + ' '
    # print(pos_count, len(exp))
    p[0] = exp
    lam_var[exp] = p[3]
    # lam_define[p[3]] = exp
    # lam_exp_record = exp
    if exp not in param_pos:
        param_pos[exp] = []
    for j in range(len(param_list)):
        param_pos[exp].append(param_list[j])    # function body的變數位置
    # param_pos[exp] = param_list
    # print(param_pos)
    pos_count = 0
    lam_flag = 0
    lam_var_record.clear()
    param_list.clear()
    lam_body.clear()
    # print('dict:', lam_define)
def p_FUN_IDs(p):
    ''' FUN_IDs : '(' ids ')'
    '''
    global lam_var_record
    if p[2] == 'null':
        p[0] = 'null'
        return
    all_id = ''
    for i in range(len(lam_var_list)):
        lam_var_record.append(lam_var_list[i])
        all_id = all_id + lam_var_list[i] + ' '
    p[0] = all_id
    lam_var_list.clear()
def p_ids(p):
    ''' ids : ids id
                | id
                |
    '''
    if p[-1] == '(' and len(p) == 1:
        p[0] = 'null'
    if len(p) == 3:
        lam_var_list.append(p[2])
    elif len(p) == 2:
        lam_var_list.append(p[1])
def p_FUN_BODY(p):
    ''' FUN_BODY : EXP
    '''
    p[0] = p[1]
def p_wait(p):
    'wait : '
    global pos_count
    if lam_flag == 1:
        lam_body.append(p[-2])
        pos_count += len(p[-2]) + 1
        lam_body.append(p[-1])
        pos_count += len(p[-1]) + 1
        return
def p_wait_one(p):
    'wait_one : '
    global pos_count
    if lam_flag == 1:
        lam_body.append(p[-1])
        if p[-1] != 'None':
            if p[-1] in lam_var_record:
                var_pos = p[-1] + ' ' + str(pos_count)
                param_list.append(var_pos)
            pos_count += len(p[-1]) + 1
        return

def p_FUN_CALL(p):
    ''' FUN_CALL : '(' FUN_EXP PARAMs ')'
                             | '(' FUN_NAME wait PARAMs ')'
    '''
    global lam_flag, pos_count
    if lam_flag == 1 and len(p) == 6:
        for i in range(len(param)):
            if param[i] != 'None':
                if param[i] in lam_var_record:
                    var_pos = param[i] + ' ' + str(pos_count)
                    param_list.append(var_pos)
                # param_list.append(pos_count)
                lam_body.append(param[i])
                pos_count += len(param[i]) + 1
        lam_body.append(p[5])
        pos_count += 2
        param.clear()
        return
    if is_id(p[2]) and is_number(define_var[p[2]]):     # function body為數字
        p[0] = define_var[p[2]]
        param.clear()
        return
    if not is_id(p[2]):     # FUN_EXP
        exp = p[2]
        var_list = lam_var[p[2]].split(' ')
    else:                   # FUN_NAME
        exp = define_var[p[2]]
        var_list = lam_var[exp].split(' ')
    v = []
    para = []
    for j in range(len(param_pos[exp])):
        p_list = param_pos[exp][j].split(' ')   # param_pos存的是 (name pos)
        v.append(p_list[0])             # name
        para.append(int(p_list[1]))     # pos

    for i in range(len(var_list) - 1):
        index = 0
        while index < len(para):
            if v[index] == var_list[i]:
                start = para[index]
                end = para[index] + len(var_list[i])
                exp = exp[:start] + param[i] + exp[end:]
                move = len(param[i]) - len(var_list[i])
                for j in range(index+1, len(para)):
                    para[j] += move
            index += 1
    # for i in range(len(var_list) - 1):
    #     exp = exp.replace(var_list[i], param[i])
    # print(exp)
    param.clear()
    lexer3 = lex.lex()
    parser3 = yacc.yacc(start='PROGRAM')
    p[0] = parser3.parse(exp, lexer=lexer3)
    # print(p[0])
def p_PARAMs(p):
    ''' PARAMs : PARAMs EXP
                         | EXP
                         |
    '''
    if len(p) == 3:
        param.append(p[2])
    elif len(p) == 2:
        param.append(p[1])
def p_LAST_EXP(p):
    ''' LAST_EXP : EXP
    '''
    p[0] = p[1]
def p_FUN_NAME(p):
    ''' FUN_NAME : id
    '''
    p[0] = p[1]

def p_error(p):
    if p:
        print("Syntax error at '%s'" % p.value)
    else:
        print("Syntax error at EOF")


# Build the lexer
lexer = lex.lex()
# Build the parser
parser = yacc.yacc(start='PROGRAM')
f = open('test_data_/09_1.lsp', 'r')
test_data = f.read()
print(test_data)
result = parser.parse(test_data)
# while True:
#     try:
#         s = input('input > ')
#     except EOFError:
#         break
#     if not s: continue
#     result = parser.parse(s)

