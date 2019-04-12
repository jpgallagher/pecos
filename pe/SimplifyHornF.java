//package edu.melbourne.z3qe;
/*Extend with mod div*/

import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Tactic;
import com.microsoft.z3.enumerations.Z3_ast_print_mode;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;

/**
 *
 * @author bishoksank
 */
public class SimplifyHornF {

    public BoolExpr eliminateQuantifiers(Context ctx, BoolExpr be) {
        Tactic t = ctx.mkTactic("qe");
        Goal g = ctx.mkGoal(false, false, false);
        g.add(be);
        BoolExpr qfFormula = ctx.mkFalse();
        Goal[] results = t.apply(g).getSubgoals();
        for (Goal res : results) {
            qfFormula = ctx.mkOr(qfFormula, res.AsBoolExpr());
        }
        return (BoolExpr) qfFormula.simplify();
    }

    public String toSMT2Benchmark(String name, BoolExpr[] assumptions, BoolExpr fmla, Context ctx) {
        // BoolExpr[] bes = new BoolExpr[0];//empty assumptions
        /*name, logic, status, attributes, assumptions, formula*/
        return ctx.benchmarkToSMTString(name, "HORN", "unknown", "", assumptions, fmla);

    }

    public BoolExpr[] readSMTLIB2File(String file, Context ctx) {
        BoolExpr[] smtFormulas = null;
        File f = new File(file);
        try {
            if (f.exists()) {
                smtFormulas = ctx.parseSMTLIB2File(file, null, null, null, null);

            } else {
                System.out.println("Error: the input file " + file + " does not exist");
                System.exit(1);
            }
        } catch (Exception e) {
            // e.printStackTrace();
            e.printStackTrace();
            System.out.println("parsing error  " + e.getLocalizedMessage());
        }
        return smtFormulas;
    }

    public static String showQEStatistics(String file, long time) {
        String output;
        output = "\n{File=" + file + ", Time=" + time + " ms}";
        return output;
    }

    public BoolExpr getBodyQFormula(Quantifier q, Symbol[] varNames, Sort[] varSorts, Context context) {
        int nrBoundVars = varNames.length;
        Expr[] varExpr = new Expr[nrBoundVars];
        for (int i = 0; i < varNames.length; i++) {
            int j = nrBoundVars - 1 - i;
            varExpr[i] = context.mkConst(varNames[j], varSorts[j]);
            //varExpr[nrBoundVars - 1 - i] = context.mkBVConst(varNames[i], ((BitVecSort) varSorts[i]).getSize()); //reversing the list
        }
        BoolExpr qBody = q.getBody(); //extential variables in the body gets renamed bottom-up in the way quantifiers are
        //https://z3prover.github.io/api/html/classcom_1_1microsoft_1_1z3_1_1_expr.html#a0550736fa88de0a0aadb801e9d1e7e73
        return (BoolExpr) qBody.substituteVars(varExpr);
    }

    public BoolExpr getFormulaWBoundVars(Context ctx, BoolExpr formula, Symbol[] varNames, Sort[] varSorts) {
        int nrBoundVars = varNames.length;
        Expr[] varExpr = new Expr[nrBoundVars];
        Expr[] boundedVars = new Expr[nrBoundVars];
        //reversal is necessary, because quantifiers are numbered inside out
        for (int i = 0; i < nrBoundVars; i++) {
            int j = nrBoundVars - 1 - i;
            varExpr[j] = ctx.mkConst(varNames[i], varSorts[i]); //reversing the list
        }
        for (int i = 0; i < nrBoundVars; i++) {
            int j = nrBoundVars - 1 - i;
            boundedVars[i] = ctx.mkBound(i, varSorts[j]); //reversing the list
        }
        return (BoolExpr) formula.substitute(varExpr, boundedVars);
    }

    boolean isBooleanConnective(BoolExpr be) {
        return (be.isAnd() || be.isOr() || be.isImplies() || be.isIff() || be.isNot() || be.isITE() || (be.isConst() && be.isBool()));
    }
    /*
     TODO: refine this, not entirely true
     */

    boolean isUserDefinedPredicate(BoolExpr be) {
        boolean retvalue = false;
        if (be.isApp()) {
            if (!isArithInEq(be) && !isBooleanConnective(be)) {
                retvalue = true;
            }
        }
        return retvalue;
    }

    /*
     input: be is body of a horn clause
     output: atoms-body atoms and
     output: constraints- body constraints
     TODO: only explores first level, no nesting
     */
    public BoolExpr[] separateBodyAtomsFromConstraints(BoolExpr be, Context ctx) {

        BoolExpr[] res = new BoolExpr[2]; //the first contains atoms, the second contains constraints
        BoolExpr tmpAtoms = ctx.mkTrue();
        BoolExpr tmpConstraints = ctx.mkTrue();
        if (be.isAnd()) {
            Expr[] exprs = be.getArgs();
            for (Expr e : exprs) {

                if (isUserDefinedPredicate((BoolExpr) e)) {
                    tmpAtoms = getConjWoTrue((BoolExpr) e, tmpAtoms, ctx);
                } else {
                    tmpConstraints = getConjWoTrue((BoolExpr) e, tmpConstraints, ctx);
                }
            }
        } else {
            //either no constraint or no atom in the body
            if (isUserDefinedPredicate((BoolExpr) be)) {
                tmpAtoms = getConjWoTrue((BoolExpr) be, tmpAtoms, ctx);
            } else {
                tmpConstraints = getConjWoTrue((BoolExpr) be, tmpConstraints, ctx);
            }
        }

        res[0] = tmpAtoms;
        res[1] = tmpConstraints;
        return res;

    }


    public ArrayList<BoolExpr> simplifyBodyConstr2DNF(BoolExpr e, Context ctx) {
        //e = preProcessQFFormulas(ctx, e);
        BoolExpr nnfF = getNNF(ctx, e);
        //System.out.println("simplified \n" + nnfF);
        //System.out.println("is tautology "+simplifyF.isTautology(nnfF, ctx));
        HashSet<BoolExpr> atomicFmla = new HashSet<>();
        collectAtomicFml(nnfF, ctx, atomicFmla);
        return simplifyMixedFormula2Disj(nnfF, ctx, atomicFmla);

    }

/* fileName is a smtlib2 file*/
    public ArrayList<BoolExpr> preprocessSMT2HornSet(String fileName) {
        Context ctx = new Context();
        BoolExpr[] be = null;
            be = readSMTLIB2File(fileName, ctx);
        
        ArrayList<BoolExpr> preProcessedHorn= new ArrayList<>();
//parsing Horn clauses
        for (BoolExpr e : be) {
            //represented as a quantified formula
            if (e.isQuantifier()) {
                Quantifier q = (Quantifier) e;
                Symbol[] varNames = q.getBoundVariableNames(); //bound variable are ordered top-down
                Sort[] varSorts = q.getBoundVariableSorts();
                e = getBodyQFormula(q, varNames, varSorts, ctx);
                //clause head and body
                if (e.isImplies()) {
                    Expr[] exprs = e.getArgs();
                    //System.out.println("head " + exprs[1]); //head is a predicate
                    //separate body atoms and constraints
                    BoolExpr body = (BoolExpr) exprs[0];
                    //atomsConstr[0] atoms; atomsConstr[1] constraints
                    BoolExpr[] atomsConstr = separateBodyAtomsFromConstraints(body, ctx);
                    ArrayList<BoolExpr> simplifiedBdyConstr = simplifyBodyConstr2DNF(atomsConstr[1], ctx);
                    //System.out.println("simlified formula "+simplifiedBdyConstr);
                    //reconstruct Horn clause 
                    for (BoolExpr siBoolExpr : simplifiedBdyConstr) {
                        BoolExpr simplifiedBdy = ctx.mkAnd(atomsConstr[0], siBoolExpr);
                        BoolExpr clause = ctx.mkImplies(simplifiedBdy, (BoolExpr) exprs[1]);
                        clause = getFormulaWBoundVars(ctx, clause, varNames, varSorts);
                        //add quantification
                        clause = ctx.mkForall(varSorts, varNames, clause, 0, null, null, null, null);
                        preProcessedHorn.add(clause);
                    }
                }else{
                    System.out.println("CASE: not handled");
                }
            }else{
            //we can have something like (assert |cp-rel-entry|)
            //(assert (not cp-rel-ERROR.i))
                preProcessedHorn.add(e);
            }
        }
        return preProcessedHorn;
    }

    void dumpStringToFile(String s, String file) {
        FileWriter fw = null;
        try {
            fw = new FileWriter(new File(file));
            fw.write(s);
        } catch (IOException ex) {
        } finally {
            try {
                fw.close();
            } catch (IOException ex) {
            }
        }
    }

    public static void main(String[] args) {
        String fileName = null;
        if (args.length >= 1) {
            fileName = args[0];
        } else {
            System.exit(1);
        }
        //create context in which formula are created
        Context ctx = new Context();
        long beginTime = System.nanoTime();
        SimplifyHornF simplifyF = new SimplifyHornF();
        BoolExpr simpForml = ctx.mkTrue();
        ArrayList<BoolExpr> simplifiedFmlaList=simplifyF.preprocessSMT2HornSet(fileName);
        BoolExpr[] simplifiedFmlaSet = simplifiedFmlaList.toArray(new BoolExpr[simplifiedFmlaList.size()]);
        String smt2Fmla = simplifyF.toSMT2Benchmark(fileName, simplifiedFmlaSet, simpForml, ctx);
        //System.out.println("smt2fmla " + smt2Fmla);
        fileName = fileName.substring(0, fileName.lastIndexOf(".smt2")) + "-simplified.smt2";
        ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB2_COMPLIANT);
        simplifyF.dumpStringToFile(smt2Fmla, fileName);
        ctx.close();
        long endTime = System.nanoTime();
        long time = endTime - beginTime;
        System.out.println("time taken " + time / 1000000 + "ms");
    }

    public BoolExpr generaliseModelToConj(Model m, Context ctx, HashSet<BoolExpr> atomicFmla) {
        BoolExpr acc = ctx.mkTrue();
        for (BoolExpr e : atomicFmla) {
            Expr evalRes = m.evaluate(e, false); /*model completion false*/

            if (evalRes.isTrue()) {
                acc = getConjWoTrue(e, acc, ctx);
            } else { //add not(e)
                if (e.isEq()) {//case not(x+y = z+w)
                    //check if x+y > z+w or x+y < z+w is satified in the model
                    Expr[] exprs = e.getArgs();
                    BoolExpr gtExpr = ctx.mkGt((ArithExpr) exprs[0], (ArithExpr) exprs[1]);
                    BoolExpr ltExpr = ctx.mkLt((ArithExpr) exprs[0], (ArithExpr) exprs[1]);
                    if (m.evaluate(gtExpr, false).isTrue()) {
                        acc = getConjWoTrue(gtExpr, acc, ctx);
                    }
                    if (m.evaluate(ltExpr, false).isTrue()) {
                        acc = getConjWoTrue(ltExpr, acc, ctx);
                    }
                } else {
                    acc = getConjWoTrue(ctx.mkNot(e), acc, ctx);
                }
            }
        }
        return acc;
    }
//acc is an accumulator

    BoolExpr getConjWoTrue(BoolExpr e, BoolExpr acc, Context ctx) {
        if (acc.isTrue()) {
            acc = e;
        } else {
            acc = ctx.mkAnd(acc, e);
        }
        return acc;
    }

    Expr[] toExprs(BoolExpr be) {
        if (be.isAnd()) {
            return be.getArgs();
        }

        Expr[] res = new Expr[1];
        res[0] = be;
        return res;
    }

    /*
     converts a conj of formula be into a hashset
     */
    HashSet<Expr> toSet(BoolExpr be) {
        HashSet<Expr> set = new HashSet<>();
        Expr[] exprs = toExprs((BoolExpr) be.simplify());
        for (Expr e : exprs) {
            if (!e.isTrue()) {
                set.add(e);
            }
        }
        return set;
    }

    /*
     converts a set of formula to a conj of formula
     */
    BoolExpr toFormula(HashSet<Expr> set, Context ctx) {
        BoolExpr be = ctx.mkTrue();
        for (Expr e : set) {
            if (be.isTrue()) {
                be = (BoolExpr) e;
            } else {
                be = ctx.mkAnd(be, (BoolExpr) e);
            }
        }
        return be;
    }

    public BoolExpr simplifyGeneralisedConj(BoolExpr origF, BoolExpr genConj, Context ctx) {
        Expr[] exprs = toExprs((BoolExpr) genConj.simplify());
        BoolExpr res;
        Solver s = ctx.mkSolver();
        Status st;
        HashSet<Expr> set;
        BoolExpr tmp;
        BoolExpr generalisedFmla; //keep tracks of the generalised formula

        for (Expr e : exprs) {
            generalisedFmla = genConj;
            set = toSet(generalisedFmla);
            set.remove(e);
            tmp = toFormula(set, ctx);
            res = ctx.mkAnd(origF, tmp);
            s.add(res);
            st = s.check();
            if (st == Status.UNSATISFIABLE) {
                //delete e from genConj
                set = toSet(genConj);
                set.remove(e);
                genConj = toFormula(set, ctx);
            }
            s.reset();
        }
        s=null;
        set=null;
        return genConj;
    }

    public boolean isTautology(BoolExpr be, Context ctx) {
        Solver s = ctx.mkSolver();
        s.add(ctx.mkNot(be));
        if (s.check() == Status.UNSATISFIABLE) {
            return true;
        }
        return false;
    }

    boolean equiv(Context ctx, BoolExpr f1, BoolExpr f2) {
        Solver s = ctx.mkSolver();
        boolean firstRes = false;
        boolean secondRes = false;
        //s.add(ctx.mkIff(f2, f1));
        s.add(ctx.mkAnd(f1, ctx.mkNot(f2)));
        Status st = s.check();
        if (st == Status.UNSATISFIABLE) {
            firstRes = true;
        }
        s.reset();
        s.add(ctx.mkAnd(f2, ctx.mkNot(f1)));
        st = s.check();
        if (st == Status.UNSATISFIABLE) {
            secondRes = true;
        }
        if (firstRes && secondRes) {
            return true;
        }
        return false;
    }

    /*
     checks if f1 => f2
     */
    boolean subsumes(BoolExpr f1, BoolExpr f2, Context ctx) {
        Solver s = ctx.mkSolver();
        s.add(ctx.mkAnd(f1, ctx.mkNot(f2)));
        if (s.check() == Status.UNSATISFIABLE) {
            return true;
        }
        s = null; //disposing solver
        return false;
    }

    public ArrayList<BoolExpr> simplifyMixedFormula2Disj(BoolExpr be, Context ctx, HashSet<BoolExpr> atomicFmla) {
        Solver s = ctx.mkSolver();
        s.add(be);
        Status st = s.check();
        int i = 0;
        ArrayList<BoolExpr> res = new ArrayList<>();
        Model m;
        while (st == Status.SATISFIABLE) {
            //System.out.println("i " + i);
            m = s.getModel();
            //generalise model to conj of atomic formulas
            BoolExpr gen1F = generaliseModelToConj(m, ctx, atomicFmla);
            // System.out.println("gen1 \n"+gen1F);
            BoolExpr gen2F = (BoolExpr) simplifyGeneralisedConj(ctx.mkNot(be), gen1F, ctx).simplify();
            //System.out.println("gen2 \n" + gen2F);
            s.add(ctx.mkNot(gen2F));
            res.add(gen2F);

            st = s.check();
            i++;
        }
        //System.out.println("nr of models "+i);
        s=null;
        return res;
    }


    void printdisj(BoolExpr be) {
        if (be.isOr()) {
            Expr[] exprs = be.getArgs();
            for (Expr e : exprs) {
                printdisj((BoolExpr) e);
                //System.out.println("disj expr "+ e.simplify());
            }
        } else {
            System.out.println("disjunct: " + be);
        }
    }

    void printconj(BoolExpr be) {
        if (be.isAnd()) {
            Expr[] exprs = be.getArgs();
            for (Expr e : exprs) {
                printconj((BoolExpr) e);
            }
        } else {
            System.out.println("conj " + be);
        }
    }

    public void collectAtomicFml(BoolExpr bExpr, Context ctx, HashSet<BoolExpr> atomicFmla) {
        Expr[] exprs;
        Expr auxBExpr;
        if (bExpr.isFalse() || bExpr.isTrue()) {
            atomicFmla.add(bExpr);
        } else if (isArithInEq(bExpr)) {
            atomicFmla.add(bExpr);

        } else if (bExpr.isNot()) { //assuming NNF
            auxBExpr = bExpr.getArgs()[0];
            collectAtomicFml((BoolExpr) auxBExpr, ctx, atomicFmla);
        } else if (bExpr.isAnd()) {
            exprs = bExpr.getArgs();
            for (int i = 0; i < exprs.length; i++) {
                collectAtomicFml((BoolExpr) exprs[i], ctx, atomicFmla);
            }
        } else if (bExpr.isOr()) {
            exprs = bExpr.getArgs();

            for (int i = 0; i < exprs.length; i++) {
                collectAtomicFml((BoolExpr) exprs[i], ctx, atomicFmla);
            }
        } else if (bExpr.isConst() && bExpr.isBool()) {
            //bExpr is a boolean variable
            atomicFmla.add(bExpr);
        } else {
            System.out.println("The Formula " + bExpr + " not recognized=== ");
        }
    }

    public boolean isArithInEq(Expr e) {
        return (e.isLE() || e.isGE() || e.isGT() || e.isLT() || e.isEq());
    }

    public BoolExpr preProcessQFFormulas(Context ctx, BoolExpr beInput) {
        Params solveEqP = ctx.mkParams();
        solveEqP.add("solve_eqs_max_occs", 2);
        Params simp2P = ctx.mkParams();
        simp2P.add("som", true);
        simp2P.add("pull_cheap_ite", true);
        simp2P.add("local_ctx", true);
        simp2P.add("local_ctx_limit", 10000000);
        simp2P.add("flat", true);
        simp2P.add("hoist_mul", false); // required by som
        Params hoistP = ctx.mkParams();
        hoistP.add("hoist_mul", true);
        hoistP.add("som", false);
//
        // used in z3
//        return and_then(
//                mk_simplify_tactic(m),
//                mk_propagate_values_tactic(m),
//                using_params(mk_solve_eqs_tactic(m), solve_eq_p),
//                mk_elim_uncnstr_tactic(m),
//                if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
//                using_params(mk_simplify_tactic(m), simp2_p),
//                using_params(mk_simplify_tactic(m), hoist_p),
//                mk_max_bv_sharing_tactic(m),
//                if_no_proofs(if_no_unsat_cores(mk_ackermannize_bv_tactic(m, p)))
//        );

        Tactic simplify = ctx.mkTactic("simplify");
        Tactic propagateValues = ctx.mkTactic("propagate-values");
        Tactic solveEqs = ctx.mkTactic("solve-eqs");
        Tactic elimUncnstr = ctx.mkTactic("elim-uncnstr");

        Tactic preamble = ctx.andThen(
                simplify,
                propagateValues,
                //ctx.usingParams(solveEqs, solveEqP), //this shows some prob., maybe does not return equiv solution
                //elimUncnstr,
                ctx.usingParams(simplify, simp2P),
                ctx.usingParams(simplify, hoistP));
        BoolExpr be = ctx.mkFalse();
        Goal g = ctx.mkGoal(false, false, false);
        g.add(beInput);
        ApplyResult ar = preamble.apply(g);

        Goal[] g1 = ar.getSubgoals();
        //System.out.println("length " + g1.length);
        if (g1.length == 1) {
            be = g1[0].AsBoolExpr();
            g = null;
            g1 = null;
            return be;
        }
        System.err.println("length greater than 1: tactic preProcessQFBVFormulas");
        System.exit(1);
        for (int i = 0; i < g1.length; i++) {
            be = ctx.mkOr(be, g1[i].AsBoolExpr());

        }

        return (BoolExpr) be.simplify();
    }

    public BoolExpr getNNF(Context ctx, BoolExpr e) {
        Tactic t = ctx.mkTactic("nnf");
        Goal g = ctx.mkGoal(false, false, false);//maGoal(model, unsacore, proofs)
//        System.out.println("orig " + e);
        BoolExpr be = ctx.mkFalse();
        g.add(e);

        ApplyResult ar = t.apply(g);
        Goal[] g1 = ar.getSubgoals();
        if (g1.length == 1) {
            be = g1[0].AsBoolExpr();
            g = null;
            g1 = null;
            return be;
        }
        if (g1.length > 1) {
            be = g1[0].AsBoolExpr();
        }
        for (int i = 1; i < g1.length; i++) {
            be = ctx.mkOr(be, g1[i].AsBoolExpr());
        }
//        System.out.println("simplied " + be);
        g = null;
        g1 = null;
        return be;
    }


}
