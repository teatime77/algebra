import { App, ConstNum, parseMath, Parser, RefVar, Term } from "@parser";
import { Formula, mathLib } from "./formula.js";
import type { PredicateNode, Theorem } from "./formula.js";
import { matchFormula, SearchMatchFormula } from "./formula_matcher.js";
import { FormulaMenuEntry, ProofStep, putStr, showFormulaMenu } from "./algebra_util";
import { assert, msg, MyError } from "@i18n";
import { mathSelection, TexSelection, toTex } from "./tex";

function parthFormulaPath(formulaSsideId: string) : [Theorem, Formula, number] {
    const items = formulaSsideId.split(".");
    assert(items.length == 3 && items[0][0] == "#");
    const [theoremId, tag, sideStr] = items;
    const theorem = mathLib.theorems.get(theoremId.slice(1));
    if(theorem == undefined){
        throw new MyError();
    }

    const formula = theorem.getFormula(tag);
    const predicate = formula.predicate
    if(predicate == undefined){
        throw new MyError();
    }

    const sideIdx = parseInt(sideStr) - 1;
    assert(0 <= sideIdx && sideIdx <= predicate.args.length - 1);

    return [theorem, formula, sideIdx];
}

function makeEqMenu(node:PredicateNode, eq : App) : FormulaMenuEntry[] {
    const items: FormulaMenuEntry[] = [];

    for(const [sideIdx, side] of eq.args.entries()){
        let name : string;

        if(sideIdx == 0){

            name = "左辺をコピー";
        }
        else if(sideIdx == eq.args.length - 1){

            name = "右辺をコピー";
        }
        else{
            name = `第${sideIdx + 1}辺をコピー`;
        }

        items.push({
            type:"action",
            step : new CopySide(node, sideIdx),
            name,
            latex: toTex(side)
        })
    }

    return items;
}

function makeFormulaMenu(formula : Formula) : FormulaMenuEntry[] {
    const items: FormulaMenuEntry[] = [];

    if(formula.predicate.isEq()){
        const eq = formula.predicate as App;

        items.push(...makeEqMenu(formula, eq) );
    }
    else{
        throw new MyError();
    }

    return items;
}

function makeProofStepMenu(step : ProofStep) : FormulaMenuEntry[] {
    const items: FormulaMenuEntry[] = [];

    if(step.getResult() instanceof App){
        const app = step.getResult() as App;
        if(app.isEq()){

            return makeEqMenu(step, app)
        }
        else{
            if(mathSelection != undefined && mathSelection.kind == "node"){
                const formulaSideIdxes = SearchMatchFormula(mathSelection.selectedTerm);
                for(const [formula, sideIdx, predicate_cp] of formulaSideIdxes){
                    assert(predicate_cp.isEq());

                    for(const [sideIdx2, side2] of predicate_cp.args.entries()){
                        if(sideIdx2 != sideIdx){
                            const rewrite = new Rewrite(step, mathSelection.selectedTerm, formula, sideIdx, predicate_cp, sideIdx2);
                            items.push({
                                type:"action",
                                step : rewrite,
                                name : `${formula.theorem.name}.${formula.tag}`,
                                latex: toTex(side2)
                            })
                        }
                    }
                }
            }
        }
    }

    return items;
}

export function makeFormulaDiv(parent:HTMLDivElement, formula: Formula) : HTMLDivElement {
    const expressDiv = document.createElement("div");
    if(formula instanceof Formula){

        putStr(expressDiv, formula.tag);
    }

    const btn = document.createElement("button");
    btn.textContent = "...";
    btn.addEventListener("click", (event:PointerEvent)=>{

        showFormulaMenu(formula,
            makeFormulaMenu(formula),
            event.clientX,
            event.clientY
        );
    });

    expressDiv.appendChild(btn);

    new TexSelection(expressDiv, formula.predicate);

    parent.appendChild(expressDiv);

    return expressDiv
}

export function makeProofStepDiv(parent:HTMLDivElement, step: ProofStep) : HTMLDivElement {
    step.nodeDiv = document.createElement("div");

    const btn = document.createElement("button");
    btn.textContent = "...";
    btn.addEventListener("click", (event:PointerEvent)=>{

        showFormulaMenu(step.proof!.formula,
            makeProofStepMenu(step),
            event.clientX,
            event.clientY
        );
    });

    step.nodeDiv.appendChild(btn);

    new TexSelection(step.nodeDiv, step.getResult());

    parent.appendChild(step.nodeDiv);

    return step.nodeDiv
}

export class CopySide extends ProofStep {
    sourceNode : PredicateNode;
    sideIdx : number;

    static makeCopySide(sourceNode : PredicateNode, proofContent : HTMLDivElement, line: string) : CopySide{
        const parser = new Parser(line.slice(1));
        const terms:Term[] = [];
        parser.readList(terms);
        terms.forEach(x => x.setString());

        assert(terms.length == 2);
        assert(terms[0] instanceof ConstNum);
        const [sideIdx, result] = terms as [ConstNum, Term];

        const step = new CopySide(sourceNode, sideIdx.int() - 1);
        if(`${step.result}` != `${result}`){
            msg(`make-copy-side:[${line}][${step.result}][${result}]`)
            throw new MyError();
        }

        return step;
    }

    constructor(sourceNode : PredicateNode, sideIdx : number){
        super(sourceNode instanceof ProofStep ? sourceNode : undefined);
        this.sourceNode = sourceNode;
        this.sideIdx = sideIdx;

        const eq = this.sourceNode.getResult() as App;
        assert(eq.isEq());

        this.result = eq.getArg(this.sideIdx).clone();
        this.result.setParent(null);
    }

    applyProofStep() : void {
        msg(`apply-copy-side:${this.sourceNode.nodeDiv.tagName}`);

        if(this.sourceNode instanceof Formula){
            const proof = this.sourceNode.addProof();
            proof.addProofStep(this);

            const parentDiv = this.sourceNode.nodeDiv;
            putStr(parentDiv, "start proof");

            makeProofStepDiv(parentDiv, this);
        }
    }

    toString() : string {
        return `© ${this.sideIdx + 1}, ${this.result}\n`;
    }
}

export class Rewrite extends ProofStep {
    target : Term;
    formula : Formula;
    sideIdx : number;
    predicate_cp : App;
    sideIdx2 : number;

    static makeRewrite(prevStep : ProofStep, proofContent : HTMLDivElement, line: string){
        const parser = new Parser(line.slice(1));
        const terms:Term[] = [];
        parser.readList(terms);
        terms.forEach(x => x.setString());
        const s = terms.map(x => `${x}`).join(", ");
        msg(`step-proof:${s}`);
        assert(terms.length == 4);
        assert(terms[1] instanceof RefVar && terms[2] instanceof ConstNum);
        const targetTmp = terms[0];
        const formulaSsideIdRef = terms[1] as RefVar;
        const sideIdx2 = (terms[2] as ConstNum).int() - 1;
        const result = terms[3];

        assert(prevStep.result != undefined);
        const targetTmpStr = `${targetTmp}`;
        const targets = prevStep.result!.allTerms().filter(x => `${x}` == targetTmpStr);
        if(targets.length != 1){
            msg(`make-rewrite:[${targetTmpStr}]`);
            prevStep.result!.allTerms().forEach(x => msg(`    [${x}]`));
            throw new MyError();
        }
        const target = targets[0];

        const [theorem, formula, sideIdx] = parthFormulaPath(formulaSsideIdRef.name);

        const paramDic = new Map<string, Term>();
        const predicate_cp = matchFormula(target, theorem, paramDic, formula, sideIdx);
        if(predicate_cp == undefined){
            throw new MyError();
        }

        const step = new Rewrite(prevStep, target, formula, sideIdx, predicate_cp, sideIdx2);
        if(`${step.result}` != `${result}`){
            msg(`make-rewrite2:[${line}][${step.result}][${result}]`)
            throw new MyError();
        }

        return step;
    }

    constructor(prevStep : ProofStep, target : Term, formula : Formula, sideIdx : number, predicate_cp : App, sideIdx2 : number){
        super(prevStep);
        this.target = target;
        this.formula = formula;
        this.sideIdx = sideIdx;

        this.predicate_cp = predicate_cp;
        this.sideIdx2 = sideIdx2;

        const [target_root_cp, target_cp] = this.target.cloneRoot();
        const side2 = this.predicate_cp.getArg(this.sideIdx2).clone();
        if(target_root_cp == target_cp){
            this.result = side2;
        }
        else{

            target_cp.replaceTerm(side2);
            this.result = target_root_cp;
        }

        this.result.setParent(null);
    }

    applyProofStep() : void {
        if(this.prevStep == undefined || this.prevStep.proof == undefined){
            throw new MyError();
        }
        const params = this.formula.theorem.params();
        if(params.length != 0){
            assert(params.length == 1 && this.result != undefined);
            const paramRefs = this.result!.allTerms().filter(x => x instanceof RefVar && x.name == "?");
            if(paramRefs.length != 0){

                const s = window.prompt("Input the expression");
                if(s == null || s.trim() == ""){
                    return;
                }
                const term = parseMath(s);
                for(const refvar of paramRefs){
                    refvar.replaceTerm(term.clone());
                }
            }
        }
        this.prevStep.proof.addProofStep(this);
        msg(`apply rewrite`);

        const parentDiv = this.prevStep!.nodeDiv;

        makeProofStepDiv(parentDiv, this);
    }

    toString() : string {
        return `@ ${this.target}, #${this.formula.theorem.name}.${this.formula.tag}.${this.sideIdx + 1}, ${this.sideIdx2 + 1}, ${this.result} \n`;
    }
}

/*
class AddBothSides extends ProofStep {
}

class MultiplyBothSides extends ProofStep {
}

class AddPlusMinusZero extends ProofStep {
}


class MultiplyFractionOne extends ProofStep {
}
*/