// L5-typecheck
// ========================================================
import { equals, map, zipWith } from 'ramda';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isStrExp, isVarRef, parseL5Exp, parseL5Program, unparse,
         AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, NumExp,
         Parsed, PrimOp, ProcExp, Program, StrExp, isLitExp, LitExp } from "./L5-ast";
import { isCompoundSExp, isEmptySExp, isSymbolSExp, valueToString } from './L5-value';
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import { isProcTExp, isPairTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
    parseTE, unparseTExp, isTVar, isAtomicTExp, makeLiteralTExp,
    BoolTExp, NumTExp, StrTExp, TExp, VoidTExp, PairTExp, makePairTExp, LiteralTExp } from "./TExp";
import { isEmpty, allT, first, rest, NonEmptyList, List, isNonEmptyList, cons } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult, isOk } from '../shared/result';
import { parse as p } from "../shared/parser";
import { format } from '../shared/format';

// Purpose: Check that type expressions are equivalent
// as part of a fully-annotated type check process of exp.
// Return an error if the types are different - true otherwise.
// Exp is only passed for documentation purposes.
const checkEqualType = (te1: TExp, te2: TExp, exp: Exp): Result<true> =>
  equals(te1, te2) ? makeOk(true) :
  bind(unparseTExp(te1), (te1: string) =>
    bind(unparseTExp(te2), (te2: string) =>
        bind(unparse(exp), (exp: string) => 
            makeFailure<true>(`Incompatible types: ${te1} and ${te2} in ${exp}`))));

// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L5typeof = (concreteExp: string): Result<string> =>
    bind(p(concreteExp), (x) =>
        bind(parseL5Exp(x), (e: Exp) => 
            bind(typeofExp(e, makeEmptyTEnv()), unparseTExp)));

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
    isBoolExp(exp) ? makeOk(typeofBool(exp)) :
    isStrExp(exp) ? makeOk(typeofStr(exp)) :
    isPrimOp(exp) ? typeofPrim(exp) :
    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
    isIfExp(exp) ? typeofIf(exp, tenv) :
    isProcExp(exp) ? typeofProc(exp, tenv) :
    isAppExp(exp) ? typeofApp(exp, tenv) :
    isLetExp(exp) ? typeofLet(exp, tenv) :
    isLetrecExp(exp) ? typeofLetrec(exp, tenv) :
    isDefineExp(exp) ? typeofDefine(exp, tenv) :
    isProgram(exp) ? typeofProgram(exp) :
    isLitExp(exp) ? typeofLit(exp) :
    // TODO: isSetExp(exp)
    makeFailure(`Unknown type: ${format(exp)}`);

// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: List<Exp>, tenv: TEnv): Result<TExp> =>
    isNonEmptyList<Exp>(exps) ? 
        isEmpty(rest(exps)) ? typeofExp(first(exps), tenv) :
        bind(typeofExp(first(exps), tenv), _ => typeofExps(rest(exps), tenv)) :
    makeFailure(`Unexpected empty list of expressions`);


// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// Purpose: compute the type of a literal expression
// All quoted expressions are treated as literal type, except for compound sexps (pairs)
const typeofLit = (exp: LitExp): Result<TExp> => {
    const val = exp.val;
    return isCompoundSExp(val) ? typeofCompoundSExp(val) :
           makeOk(makeLiteralTExp());  // Everything in quotes is literal
};

// Purpose: compute the type of a compound S-expression (for pairs)
const typeofCompoundSExp = (val: any): Result<TExp> => {
    if (isCompoundSExp(val)) {
        // For pairs like (4 . 7), determine types recursively
        const leftType = typeof val.val1 === 'number' ? makeNumTExp() :
                        typeof val.val1 === 'boolean' ? makeBoolTExp() :
                        typeof val.val1 === 'string' ? makeStrTExp() :
                        isSymbolSExp(val.val1) ? makeLiteralTExp() :
                        makeLiteralTExp();
        
        const rightType = typeof val.val2 === 'number' ? makeNumTExp() :
                         typeof val.val2 === 'boolean' ? makeBoolTExp() :
                         typeof val.val2 === 'string' ? makeStrTExp() :
                         isSymbolSExp(val.val2) ? makeLiteralTExp() :
                         makeLiteralTExp();
        
        return makeOk(makePairTExp(leftType, rightType));
    }
    return makeOk(makeLiteralTExp());
};

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');


export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
    (p.op === '-') ? numOpTExp :
    (p.op === '*') ? numOpTExp :
    (p.op === '/') ? numOpTExp :
    (p.op === 'and') ? boolOpTExp :
    (p.op === 'or') ? boolOpTExp :
    (p.op === '>') ? numCompTExp :
    (p.op === '<') ? numCompTExp :
    (p.op === '=') ? numCompTExp :
    // Important to use a different signature for each op with a TVar to avoid capture
    (p.op === 'number?') ? parseTE('(T -> boolean)') :
    (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
    (p.op === 'string?') ? parseTE('(T -> boolean)') :
    (p.op === 'list?') ? parseTE('(T -> boolean)') :
    (p.op === 'pair?') ? parseTE('(T -> boolean)') :
    (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
    (p.op === 'not') ? parseTE('(boolean -> boolean)') :
    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'display') ? parseTE('(T -> void)') :
    (p.op === 'newline') ? parseTE('(Empty -> void)') :
    // Pair ops
    (p.op === 'cons') ? parseTE('(T1 * T2 -> (Pair T1 T2))') :
    (p.op === 'car') ? parseTE('((Pair T1 T2) -> T1)') :
    (p.op === 'cdr') ? parseTE('((Pair T1 T2) -> T2)') :
    makeFailure(`Primitive not yet implemented: ${p.op}`);

// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1
export const typeofIf = (ifExp: IfExp, tenv: TEnv): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv);
    const thenTE = typeofExp(ifExp.then, tenv);
    const altTE = typeofExp(ifExp.alt, tenv);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp));
    const constraint2 = bind(thenTE, (thenTE: TExp) =>
                            bind(altTE, (altTE: TExp) =>
                                checkEqualType(thenTE, altTE, ifExp)));
    return bind(constraint1, (_c1: true) =>
                bind(constraint2, (_c2: true) =>
                    thenTE));
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv), (body: TExp) => 
                            checkEqualType(body, proc.returnTE, proc));
    return bind(constraint1, _ => makeOk(makeProcTExp(argsTEs, proc.returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv): Result<TExp> =>
    bind(typeofExp(app.rator, tenv), (ratorTE: TExp) => {
        if (! isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                        bind(unparse(app), (exp: string) =>
                            makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        
        // Type unification במקום checkEqualType
        const substitution = new Map<string, TExp>();
        
        for (let i = 0; i < app.rands.length; i++) {
            const randTEResult = typeofExp(app.rands[i], tenv);
            if (!isOk(randTEResult)) return randTEResult;
            
            const paramTE = ratorTE.paramTEs[i];
            const randTE = randTEResult.value;
            
            if (!unifyTypes(paramTE, randTE, substitution)) {
                return bind(unparse(app), (exp: string) => 
                    makeFailure<TExp>(`Type mismatch in application: ${exp}`));
            }
        }
        
        // החלף Type Variables בטיפוס המוחזר
        return makeOk(substituteTypeVars(ratorTE.returnTE, substitution));
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv), (typeOfVal: TExp) => 
                                                            checkEqualType(varTE, typeOfVal, exp)),
                                      varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv)));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (! allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${format(exp)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
                           paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) => 
                            zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody));
};

// Typecheck a full program
// TODO: Thread the TEnv (as in L1)

// Purpose: compute the type of a define
// Typing rule:
//   (define (var : texp) val)
// TODO - write the true definition
export const typeofDefine = (exp: DefineExp, tenv: TEnv): Result<VoidTExp> => {
    const valTE = typeofExp(exp.val, tenv)
    const constraint = bind(valTE, (valType: TExp) => checkEqualType(valType, exp.var.texp, exp));
    return isOk(constraint) ? makeOk(makeVoidTExp()) : makeFailure("VarDecl type different from val type, types:" +
                                                 (isOk(valTE) ? unparseTExp(valTE.value) : "unknown") + " and " + unparseTExp(exp.var.texp));
};

// Purpose: compute the type of a program
// Typing rule:
// TODO - write the true definition
export const typeofProgram = (exp: Program): Result<TExp> =>{
    const exps = exp.exps;

    const recur = (remaining: Exp[], env: TEnv): Result<TExp> => 
        (isEmpty(remaining)) ? makeOk(makeVoidTExp()) :
        (remaining.length === 1) ? typeofExp(remaining[0], env) :
        (isDefineExp(remaining[0])) ? bind(typeofDefine(remaining[0], env), (_) => recur(remaining.slice(1), makeExtendTEnv([(remaining[0] as DefineExp).var.var], [(remaining[0] as DefineExp).var.texp], env))) :
        bind(typeofExp(remaining[0], env), (_) => recur(remaining.slice(1), env));
    
    return recur(exps, makeEmptyTEnv());
};

export const L5programTypeof = (exp: string): Result<string> =>
    (exp.length >= 5) && (exp.substring(0, 4) === "(L5 ") && (exp.substring(exp.length - 1) === ")") ?
        bind(p(exp), (x) =>
            bind(parseL5Program(x), (prog: Program) =>
                bind(typeofProgram(prog), unparseTExp))) :
        makeFailure(`Invalid L5 program: ${exp}`);

// Type unification functions
const unifyTypes = (expected: TExp, actual: TExp, substitution: Map<string, TExp>): boolean => {
    if (isTVar(expected)) {
        const existing = substitution.get(expected.var);
        if (existing) {
            return equals(existing, actual);
        }
        substitution.set(expected.var, actual);
        return true;
    }
    
    if (isAtomicTExp(expected) && isAtomicTExp(actual)) {
        return equals(expected, actual);
    }
    
    if (isPairTExp(expected) && isPairTExp(actual)) {
        return unifyTypes(expected.first, actual.first, substitution) &&
               unifyTypes(expected.second, actual.second, substitution);
    }
    
    return equals(expected, actual);
};

const substituteTypeVars = (type: TExp, substitution: Map<string, TExp>): TExp => {
    if (isTVar(type)) {
        return substitution.get(type.var) || type;
    }
    
    if (isPairTExp(type)) {
        return makePairTExp(
            substituteTypeVars(type.first, substitution),
            substituteTypeVars(type.second, substitution)
        );
    }
    
    if (isProcTExp(type)) {
        return makeProcTExp(
            type.paramTEs.map(p => substituteTypeVars(p, substitution)),
            substituteTypeVars(type.returnTE, substitution)
        );
    }
    
    return type;
};