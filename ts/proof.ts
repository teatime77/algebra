import { assert, msg } from "@i18n";
import { RefVar, App, Term } from "@parser";
import type { Formula } from "./formula.js";
import type { ProofStep } from "./algebra_util.js";

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
}

export abstract class Transformation {
    commandName : string;

    constructor(command_name : string){
        this.commandName     = command_name;
    }
}
