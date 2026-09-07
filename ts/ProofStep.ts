import { Term } from "@parser";
import { Formula } from "./formula";
import { ProofStep } from "./algebra_util";

class FormulaStep extends ProofStep {
    formula : Formula;
    sideIdx : number;

    constructor(formula : Formula, sideIdx : number){
        super();
        this.formula = formula;
        this.sideIdx = sideIdx;
    }
}

export class CopySide extends FormulaStep {
    constructor(formula : Formula, sideIdx : number){
        super(formula, sideIdx);
    }
}

export class CopyTerm extends ProofStep {
    
}

export class Rewrite extends FormulaStep {
    root : Term;
    target : Term;

    constructor(formula : Formula, sideIdx : number, root : Term, target : Term){
        super(formula, sideIdx);
        this.root   = root;
        this.target = target;
    }
}

class AddBothSides extends ProofStep {
}

class MultiplyBothSides extends ProofStep {
}

class AddPlusMinusZero extends ProofStep {
}


class MultiplyFractionOne extends ProofStep {
}
