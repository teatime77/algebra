import { App, Term } from "@parser";
import { Formula, PredicateNode, SearchMatchFormula } from "./formula";
import { DummyStep, FormulaMenuEntry, ProofStep, putStr, showFormulaMenu } from "./algebra_util";
import { assert, msg, MyError } from "@i18n";
import { mathSelection, TexSelection } from "./tex";

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
            latex: side.tex()
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
                            const rewrite = new Rewrite(step, mathSelection.selectedTerm, formula.predicate, sideIdx, predicate_cp, sideIdx2);
                            items.push({
                                type:"action",
                                step : rewrite,
                                name : `${formula.theorem.name}.${formula.tag}`,
                                latex: side2.tex()
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

        showFormulaMenu(
            makeFormulaMenu(formula),
            event.clientX,
            event.clientY,
            (item) => {
                msg(`selected:${item.name}`);
            },
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

        showFormulaMenu(
            makeProofStepMenu(step),
            event.clientX,
            event.clientY,
            (item) => {
                msg(`selected:${item.name}`);
            },
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
            const parentDiv = this.sourceNode.nodeDiv;
            putStr(parentDiv, "start proof");

            makeProofStepDiv(parentDiv, this);
        }
    }
}

export class Rewrite extends ProofStep {
    target : Term;
    predicate_cp : App;
    sideIdx2 : number

    constructor(prevStep : ProofStep, target : Term, predicate : App, sideIdx : number, predicate_cp : App, sideIdx2 : number){
        super(prevStep);
        this.target = target;
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
        assert(this.prevStep != undefined);
        msg(`apply rewrite`);

        const parentDiv = this.prevStep!.nodeDiv;

        makeProofStepDiv(parentDiv, this);
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