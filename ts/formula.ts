import { assert, msg, fetchText, MyError, $div } from "@i18n";
import { RefVar, App, parseMath, Term, isLetter, Variable, Binding } from "@parser";
import { allTerms } from "./algebra_util.js";
import { Proof } from "./proof.js";

const sysVarNames : string[] = [
    "∞",
    "π",
    "limit",
    "diff",
    "integrate",
    "sin",
    "cos",
    "tan",
    "sqrt",
    "root",
];

let sysVars : Variable[] = [];

export function initSysVars(){
    sysVars = sysVarNames.map(x => new Variable(x, undefined, undefined));
}

export interface PredicateNode {
    getResult() : Term;
    nodeDiv : HTMLDivElement;
}

export class Formula implements PredicateNode {
    static formulaIdx = 0;
    idx : number;
    theorem : Theorem;
    tag : string;
    predicate : App;
    proofs : Proof[] = [];
    nodeDiv : HTMLDivElement;
    str : string;

    constructor(theorem : Theorem, predicate : App, formulaDiv : HTMLDivElement){
        this.idx = Formula.formulaIdx++;
        this.theorem = theorem;
        this.predicate = predicate;
        this.nodeDiv = formulaDiv;
        this.str = `${predicate}`;
        this.tag = `${theorem.formulas.size + 1}`;

        theorem.setRefVars(predicate);
    }

    getResult() : Term {
        return this.predicate;
    }

    addProof() : Proof {
        const proof = new Proof(this);
        this.proofs.push(proof);

        return proof;
    }

    startProof() : Proof {
        const proof = new Proof(this);
        this.proofs.push(proof);

        return proof;
    }

    lastProof() : Proof {
        return this.proofs.at(-1)!;
    }

    toString() : string {
        let str = `${this.predicate}\n\n`;

        for(const proof of this.proofs){
            str += "proof\n";
            str += proof.proofSteps.map(x => `${x}`).join("");
            str += "qed\n";
        }

        return str;
    }    
}

export class VarDecl {
    kind : string;
    vars : Variable[] = [];

    constructor(kind : string){
        this.kind = kind;
    }

    toString() : string {
        if(this.vars[0].type != undefined && this.vars.every(x => x.type != undefined && `${x.type}` == `${this.vars[0].type}`)){
            return `    ${this.kind} ${this.vars.map(x => x.name).join(", ")} : ${this.vars[0].type}\n`;
        }
        else{
            assert(this.vars.length == 1);
            const va = this.vars[0];

            let str = `    ${this.kind} ${va.name}`;
            if(va.type != undefined){
                str += ` : ${va.type}`;
            }
            if(va.init != undefined){
                str += ` = ${va.init}`;
            }

            return str + "\n";
        }
    }

}

export class Theorem {
    kind : string;
    name : string;
    varDecls : VarDecl[] = [];
    formulas = new Map<string, Formula>();
    theoremDiv : HTMLDivElement;
    comments : string[];

    constructor(comments : string[], kind : string, name : string){
        this.comments = comments;
        this.kind = kind;
        this.name = name;

        this.theoremDiv = document.createElement("div");

        const title = document.createElement("h5");
        title.textContent = this.name;
        this.theoremDiv.appendChild(title);

        $div("formula-book").appendChild(this.theoremDiv);
    }

    params() : Variable[] {
        return this.varDecls.filter(vd => vd.kind == "param").map(vd => vd.vars).flat();
    }

    lastFormula() : Formula {
        return Array.from(this.formulas.values()).at(-1)!;
    }

    addFormula(formula: Formula){

        this.formulas.set(formula.tag, formula);

        assert(this.lastFormula() === formula);
    }

    getFormula(id:string) : Formula {
        const formula = this.formulas.get(id);
        if(formula == undefined){
            throw new MyError();
        }

        return formula;
    }

    toString() : string {
        let str = "";

        if(this.comments.length != 0){
            str += this.comments.join("\n") + "\n";
        }

        str += `${this.kind} ${this.name}\n`;

        if(this.varDecls.length != 0){
            str += this.varDecls.map(x => x.toString()).join("");
            str += "\n";
        }

        str += Array.from(this.formulas.values()).map(x => `${x}`).join("");

        return str;
    }

    setRefVars(root : Term){
        const variables = this.varDecls.map(x => x.vars).flat().concat(sysVars);
        const all_refs = allTerms(root).filter(x => x instanceof RefVar && isLetter(x.name[0])) as RefVar[];
        for(const ref of all_refs){
            
            for(let app = ref.parent; app != null; app = app.parent){
                if(app instanceof Binding){
                    ref.refVar = app.vars.find(x => x.name == ref.name);
                    if(ref.refVar != undefined){
                        break;
                    }
                }
            }
            if(ref.refVar == undefined){

                ref.refVar = variables.find(x => x.name == ref.name);
            }
            if(ref.refVar == undefined){

                msg(`ref-var:${ref.name} in [${root}]`);
            }
            // assert(ref.refVar != undefined, `ref-var:${ref.name}`);
        }
    }
}

export class MathLib {
    name! : string;
    theorems : Map<string, Theorem> = new Map<string, Theorem>();

    clear(){
        this.theorems.clear();
    }

    toString() : string{
        let str = `namespace ${this.name}\n\n`;
        str += Array.from(this.theorems.values()).map(x => x.toString()).join("");

        return str;
    }
}

export const mathLib = new MathLib();

function actionRef(name : string) : RefVar {
    return new RefVar(name);
}

class Index {
    id       : number;
    assertion : App;

    constructor(id : number, assertion_str : string){
        this.id = id;
        this.assertion = parseMath(assertion_str) as App;
    }
}

class TermSelection{
    app : App;
    start : number;
    end   : number;

    constructor(app : App, start : number, end   : number){
        this.app   = app;
        this.start = start;
        this.end   = end;
    }
}

let Indexes : Index[] = [];
let curIndex : Index | undefined;

async function readFormulas(){
    Indexes = [];

    const text = await fetchText(`../data/formulas.txt`);
    const lines = text.split('\r\n').map(x => x.trim()).filter(x => x.length != 0);
    for(const line of lines){
        const i = line.indexOf(':');
        const id = parseInt( line.substring(0, i).trim() )!;
        const assertion_str = line.substring(i + 1).trim();

        const index = new Index(id, assertion_str);
        Indexes.push(index);
    }
}

function enumFormulasForTermSelection(sel : TermSelection){

}

function enumFormulasForEquation(sel : TermSelection){

}

function enumFormulasForTerm(sel : TermSelection){

}

function enumFormulasForTerms(sel : TermSelection){

}
