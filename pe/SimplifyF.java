package edu.melbourne.z3qe;
/*Extend with mod div*/

import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Goal;
import com.microsoft.z3.Model;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Tactic;
import java.io.File;
import java.util.HashSet;

/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
/**
 *
 * @author bishoksank
 */
public class SimplifyF {

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

    public static void main(String[] args) {
        String fileName = null;
        BoolExpr[] be = null;
        if (args.length >= 1) {
            fileName = args[0];
        } else {
            System.exit(1);
        }
        Context ctx = new Context();
        SimplifyF simplifyF = new SimplifyF();
        if (fileName.endsWith(".smt")) {
            //be = simplifyF.readSMTLIB1File(fileName, ctx);
        } else {
            be = simplifyF.readSMTLIB2File(fileName, ctx);
        }
        long beginTime = System.nanoTime();
        for (BoolExpr e : be) {
            e = simplifyF.preProcessQFFormulas(ctx, e);
            BoolExpr nnfF = simplifyF.getNNF(ctx, e);
            //    System.out.println("simplified \n" + nnfF);
            //System.out.println("is tautology "+simplifyF.isTautology(nnfF, ctx));
            HashSet<BoolExpr> atomicFmla = new HashSet<>();
            simplifyF.collectAtomicFml(nnfF, ctx, atomicFmla);
            simplifyF.simplifyMixedFormula(nnfF, ctx, atomicFmla);
        }
        long endTime = System.nanoTime();
        long time = endTime - beginTime;
        System.out.println("time taken " + time / 1000000 + "ms");
    }

    public BoolExpr generaliseModelToConj(Model m, Context ctx, HashSet<BoolExpr> atomicFmla) {
        BoolExpr acc = ctx.mkTrue();
        //ArithExpr one = ctx.mkInt(1);
        //ArithExpr zero = ctx.mkInt(0);

        for (BoolExpr e : atomicFmla) {
            Expr evalRes = m.evaluate(e, false); /*model completion false*/

            if (evalRes.isTrue()) {
                //converting Boolvar b to b=1 
//                if (e.isConst()) {
//                    acc = getConjWoTrue(ctx.mkEq(ctx.mkIntConst(e.toString()), one), acc, ctx);
//                } else {
                acc = getConjWoTrue(e, acc, ctx);
                //}
            } else { //add not(e)
//                if (e.isConst()) {
//                    
//                    acc = getConjWoTrue(ctx.mkEq(ctx.mkIntConst(e.toString()), zero), acc, ctx);
//                } else {
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
                //}
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

//    public BoolExpr simplifyGeneralisedConj(BoolExpr origF, BoolExpr genConj, Context ctx) {
//        Expr[] exprs = toExprs((BoolExpr) genConj.simplify());
//        BoolExpr res;
//        Solver s = ctx.mkSolver();
//        Status st;
//        HashSet<Expr> set;
//
//        for (Expr e : exprs) {
//            System.out.println("e " + e);
//            res = ctx.mkAnd(origF, ctx.mkNot((BoolExpr) e)); //origF /\ neg(e)
//            res = ctx.mkAnd(res, genConj);
//            s.add(res);
//            st = s.check();
//            if (st == Status.UNSATISFIABLE) {
//                //delete e from genConj
//                set = toSet(genConj);
//                System.out.println("before "+genConj);
//                set.remove(e);
//                System.out.println("considered e "+e);
//                genConj = toFormula(set, ctx);
//                System.out.println("after "+genConj);
//            }
//            s.reset();
//        }
//        return genConj;
//    }
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

    public BoolExpr simplifyMixedFormula(BoolExpr be, Context ctx, HashSet<BoolExpr> atomicFmla) {
        Solver s = ctx.mkSolver();
        s.add(be);
        Status st = s.check();
        //BoolExpr acc = ctx.mkTrue();
        BoolExpr simpF = ctx.mkFalse();
        int i = 0;
        Model m;
        while (st == Status.SATISFIABLE) {
            //System.out.println("i " + i);
            m = s.getModel();
            //generalise model to conj of atomic formulas
            BoolExpr gen1F = generaliseModelToConj(m, ctx, atomicFmla);
            // System.out.println("gen1 \n"+gen1F);
            BoolExpr gen2F = simplifyGeneralisedConj(ctx.mkNot(be), gen1F, ctx);
            //System.out.println("gen2 \n" + gen2F);
            s.add(ctx.mkNot(gen2F));
            if (simpF.isFalse()) {
                simpF = gen2F;
            } else {
                //      System.out.println("f1 "+gen2F);
                //    System.out.println("f2 "+ simpF);
                //if (!subsumes(gen2F, simpF, ctx)) {
                    //System.out.println("entered "+i);
                    simpF = ctx.mkOr(simpF, gen2F);
                //}
            }
            st = s.check();
            i++;
        }

        System.out.println(
                "nr of models " + i);
        //System.out.println("orig form " + be.isAnd() + " "+ be.getNumArgs());
        //System.out.println("simp form " + simpF.isOr()+ " "+ simpF.getNumArgs());
        System.out.println(
                " is equiv " + equiv(ctx, simpF, be));
        System.out.println(
                "conj::::");
        //printconj(be);

        System.out.println(
                "disj::::");
       // System.out.println("orign "+be);
        //System.out.println("simpF "+simpF);
        printdisj(simpF);
        return simpF;
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

    public BoolExpr getDNF(Context ctx, BoolExpr e) {
        Tactic t = ctx.mkTactic("dnf");
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
