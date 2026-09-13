import { assert, msg, MyError } from "@i18n";
import { RefVar, App, Term, Parser } from "@parser";
import type { Formula, Theorem } from "./formula.js";
import { mathLib } from "./formula.js";
import type { ProofStep } from "./algebra_util.js";
import { allTerms, putStr, putTex, setHashTerm2 } from "./algebra_util.js";
import { matchFormula } from "./formula_matcher.js";

function isExpressionNumber(term : Term) : term is App {
    return term instanceof App && term.fncName == "." && term.args[0] instanceof RefVar && term.args[0].name.startsWith("#");
}

function getTermInApply(prevExpr : App, t : Term){
    if(isExpressionNumber(t)){
        assert(t.args[1] instanceof RefVar);
        const ref1 = t.args[0] as RefVar;
        const ref2 = t.args[1] as RefVar;
        assert(ref1.name == "#0" && ref2.name == "L");

        return prevExpr.leftSide();
    }
    else{
        return t;
    }
}

function parthFormulaPath(app: App) : [Theorem, Formula, number] {
    assert(app.fncName == "." && app.args.length <= 3 && app.args.every(x => x instanceof RefVar));
    const names = (app.args as RefVar[]).map(x => x.name);
    const theorem = mathLib.theorems.get(names[0]);
    if(theorem == undefined){
        throw new MyError();
    }

    const formula = theorem.getFormula(names[1]);
    const predicate = formula.predicate
    if(predicate == undefined){
        throw new MyError();
    }

    let sideIdx : number;
    if(app.args.length == 2){

        sideIdx = 0;
    }
    else{

        const sideName = (app.args[2] as RefVar).name;
        switch(sideName){
        case "L": sideIdx = 0; break;
        case "R": sideIdx = predicate.args.length - 1; break;
        default:
            sideIdx = parseInt(sideName) - 1;
            assert(0 <= sideIdx && sideIdx <= predicate.args.length - 1);
            break;
        }
    }


    return [theorem, formula, sideIdx];
}

export class Proof {
    formula : Formula;
    proofSteps : ProofStep[] = [];
    prevExpr : Term;

    constructor(formula : Formula){
        this.formula = formula;
        this.prevExpr = formula.predicate;
        msg(`new proof:${formula.predicate}`);
    }

    addProofStep(step : ProofStep){
        step.setProof(this);
        this.proofSteps.push(step);
    }

    stepProof(proofContent : HTMLDivElement, line: string){
        const parser = new Parser(line.slice(1));
        const terms:Term[] = [];
        parser.readList(terms);
        const s = terms.map(x => `${x}`).join(", ");
        msg(`proof:${s}`);
        return;
/*
        const formulaPath = terms.shift();
        assert(formulaPath instanceof App);

        const [theorem, formula, sideIdx] = parthFormulaPath(formulaPath as App);
        for(const param of theorem.params()){
            assert(terms.length != 0);
            const term = terms.shift()!;
            param.init = term;
        }

        let target : Term;

        let root : Term;
        if(terms.length == 0){

            target = this.prevExpr.clone();
            root   = target;
        }
        else{
            if(!(this.prevExpr instanceof App)){
                throw new MyError();
            }

            target = getTermInApply(this.prevExpr, terms.shift()!).clone();

            if(terms.length == 0){

                root = this.prevExpr.clone();
            }
            else{

                root = getTermInApply(this.prevExpr, terms.shift()!).clone();
                                        
                assert(terms.length == 0);
            }

            if(root != target){

                setHashTerm2(root);
                setHashTerm2(target);
                const target2 = allTerms(root).find(x => x.hash == target.hash);
                if(target2 == undefined){
                    msg(`hash:[${root}][${target}]`);
                }
                assert(target2 != undefined);
                target = target2!;
            }
        }

        const predicate_cp = matchFormula(target, theorem, formula, sideIdx)!;
        assert(predicate_cp != undefined);

        const formula_R = predicate_cp.getArg(1 - sideIdx);
        if(target == root){
            root = formula_R;
        }
        else{

            target.replaceTerm(formula_R);
        }

        assert(proofContent != undefined);
        putStr(proofContent, line);
        putTex(proofContent, root);

        this.prevExpr = root;

        msg(`apply:[${this.prevExpr}]`);        
*/
    }
}

export abstract class Transformation {
    commandName : string;

    constructor(command_name : string){
        this.commandName     = command_name;
    }
}
