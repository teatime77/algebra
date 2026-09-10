import { assert, msg, fetchText, MyError } from "@i18n";
import { RefVar, App, parseMath, Term, ConstNum, isLetter, Variable, Parser } from "@parser";
import { allTerms, ProofStep, putStr, putTex, setHashTerm2 } from "./algebra_util.js";


export const theorems : Map<string, Theorem> = new Map<string, Theorem>();

class FormulaError extends Error {    
}


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
    const theorem = theorems.get(names[0]);
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
    }

    stepProof(proofContent : HTMLDivElement, line: string){
        const parser = new Parser(line.slice(1));
        const terms:Term[] = [];
        parser.readList(terms);
        const s = terms.map(x => x.toString()).join(", ");

        const formulaPath = terms.shift();
        assert(formulaPath instanceof App);

        const [theorem, formula, sideIdx] = parthFormulaPath(formulaPath as App);
        for(const param of theorem.params){
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
    }
}

export interface PredicateNode {
    getResult() : Term;
    nodeDiv : HTMLDivElement;
}

export class Formula implements PredicateNode {
    theorem : Theorem;
    tag : string;
    predicate : App;
    proofs : Proof[] = [];
    nodeDiv : HTMLDivElement;

    constructor(theorem : Theorem, tag : string, predicate : App, formulaDiv : HTMLDivElement){
        this.theorem = theorem;
        this.tag = tag;
        this.predicate = predicate;
        this.nodeDiv = formulaDiv;
    }

    getResult() : Term {
        return this.predicate;
    }

    startProof(){
        const proof = new Proof(this);
        this.proofs.push(proof);
    }

    lastProof() : Proof {
        return this.proofs.at(-1)!;
    }
}

export class Theorem {
    name : string;
    vars : Variable[] = [];
    params : Variable[] = [];
    formulas = new Map<string, Formula>();

    constructor(name : string){
        this.name = name;
    }

    lastFormula() : Formula {
        return Array.from(this.formulas.values()).at(-1)!;
    }

    makeHtml(): HTMLDivElement {
        const div = document.createElement("div");

        const title = document.createElement("h5");
        title.textContent = this.name;
        div.appendChild(title);

        return div;
    }

    addFormula(id : string, formula: Formula){
        if(this.formulas.has(id)){
            throw new MyError();
        }

        this.formulas.set(id, formula);

        assert(this.lastFormula() === formula);
    }

    getFormula(id:string) : Formula {
        const formula = this.formulas.get(id);
        if(formula == undefined){
            throw new MyError();
        }

        return formula;
    }
}

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

export abstract class Transformation {
    commandName : string;

    constructor(command_name : string){
        this.commandName     = command_name;
    }
}

/**
 * 
 * @param dic 変換辞書
 * @param trm1 フォーカス側の項
 * @param trm2 公式側の項
 */
function matchTerm(dic : Map<string, Term>, fdic : Map<string, [App, Term]>, focus: Term, trm1 : Term, trm2 : Term){
    if(trm2 instanceof RefVar){
        // 公式側が変数参照の場合

        if(! isLetter(trm2.name[0])){
            // 公式側が演算子の場合

            if(! trm1.eq(trm2)){
                // 等しくない場合

                throw new FormulaError();
            }
        }
        else{
            // 公式側が変数の場合

            // 変換値
            const conv = dic.get(trm2.name);
    
            if(conv == undefined){
                // 変換値が未定の場合
    
                // 新しい変換値をセットする。
                const trm1_cp = trm1.clone();

                // 変換値を変数参照の係数で割る。
                trm1_cp.value.setdiv(trm2.value);

                dic.set(trm2.name, trm1_cp);
            }
            else{
                // 変換値が既定の場合
    
                if(! trm1.eq(conv)){
                    // 変換値と等しくない場合
    
                    throw new FormulaError();
                }
            }
        }
    }
    else if(trm2 instanceof ConstNum){
        // 定数の場合

        if(! trm1.eq(trm2)){
            // 定数に等しくない場合

            throw new FormulaError();
        }
    }
    else if(trm2 instanceof App){
        // 公式側が関数呼び出しの場合

        if(trm1 instanceof App){
            // フォーカス側が関数呼び出しの場合

            if(trm2.fnc instanceof RefVar && trm2.fnc.isNamedFnc() && trm1.fnc.isOprFnc()){
                // 公式側の関数が変数で、フォーカス側の関数が演算子の場合

                // 変換値
                const conv = fdic.get(trm2.fnc.name);
                if(conv == undefined){
                    // 変換値が未定の場合
        
                    // 新しい変換値をセットする。
                    const trm1_cp = trm1.clone();
                    fdic.set(trm2.fnc.name, [trm2.clone(), trm1_cp]);
                }
                else{
                    // 変換値が既定の場合

                    // 公式側の関数呼び出しの文字表記と、変換値を得る。
                    const [trm2_cp, trm1_conv] = conv;

                    if(trm2.eq(trm2_cp)){
                        // 公式側の関数の引数が一致する場合

                        if(! trm1.eq(trm1_conv)){
                            // 変換値と等しくない場合
            
                            throw new FormulaError();
                        }        
                    }
                    else{
                        // 公式側の関数の引数が違う場合
        
                        // 未実装としてエラーにする。
                        throw new FormulaError();
                    }
                }
            }
            else{

                // 関数をマッチさせる。
                matchTerm(dic, fdic, focus, trm1.fnc, trm2.fnc);
    
                if(trm1.args.length != trm2.args.length){
                    // 引数の数が等しくない場合
    
                    throw new FormulaError();
                }
    
                // それぞれの引数をマッチさせる。
                for(const [i, t] of Array.from(trm2.args).entries()){
                    matchTerm(dic, fdic, focus, trm1.args[i], t);
                }

                if(! trm1.value.eq(trm2.value) && trm1 != focus){
                    throw new FormulaError();
                }
            }
        }
        else{
            // 関数呼び出しでない場合

            throw new FormulaError();
        }
    }
    else{
        assert(false);
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

export function substByDic(dic : Map<string, Term>, fdic : Map<string, [App, Term]>, root : App){
    const all_terms = allTerms(root);

    const apps = all_terms.filter(x => x instanceof App && fdic.has(x.fncName)) as App[];
    for(const trm2 of apps){
        const [trm2_cp, trm1_conv] = fdic.get(trm2.fncName)!;
        if(trm2.equal(trm2_cp)){
            // 公式側の関数呼び出しと一致する場合

            trm2.replaceTerm(trm1_conv.clone());
        }
        else{
            // 公式側の関数呼び出し違う場合

            // 未実装としてエラーにする。
            throw new FormulaError();
        }
    }

    const refs = all_terms.filter(x => x instanceof RefVar && dic.has(x.name)) as RefVar[];
    for(const ref of refs){
        const trm = dic.get(ref.name)!.clone();

        // 変換値に変数参照の係数をかける。
        trm.value.setmul(ref.value);

        // 変数参照を変換値で置き換える。
        ref.replaceTerm(trm);
    }
}



export function matchFormula(target : Term, theorem:Theorem, formula: Formula, sideIdx : number) : App | undefined {
    assert(formula.predicate.isEq());
    const side = formula.predicate.args[sideIdx];
    if(target instanceof App && side instanceof App){
        if(target.fncName == side.fncName && target.args.length == side.args.length){

            const [predicate_cp, side_cp] = side.cloneRoot() as [App, App];

            const dic = new Map<string, Term>();
            const fdic = new Map<string, [App, Term]>();

            for(const param of theorem.params){
                dic.set(param.name, param.init!);
            }
            try{
                matchTerm(dic, fdic, target, target, side_cp);

                substByDic(dic, fdic, predicate_cp);

                msg(`form : OK ${target} F:${predicate_cp}`);

                return predicate_cp;
            }
            catch(e){
                if(e instanceof FormulaError){

                    msg(`form : NG ${target.str()}`);
                }
                else{
                    assert(false);
                }
            }
        }
    }

    return undefined;
}

export function SearchMatchFormula(target : Term) : [Formula, number, App][] {
    const formulaSideIdxes :[Formula, number, App][] = [];

    for(const [name, theorem] of theorems.entries()){
        for(const [id, formula] of theorem.formulas.entries()){
            if(formula.predicate.isEq()){
                const eq = formula.predicate as App;
                for(const [sideIdx, side] of eq.args.entries()){
                    const predicate_cp = matchFormula(target, theorem, formula, sideIdx);
                    if(predicate_cp != undefined){

                        formulaSideIdxes.push([formula, sideIdx, predicate_cp]);
                    }
                }
            }
        }
    }

    return formulaSideIdxes;
}

function enumFormulasForTermSelection(sel : TermSelection){

}

function enumFormulasForEquation(sel : TermSelection){

}

function enumFormulasForTerm(sel : TermSelection){

}

function enumFormulasForTerms(sel : TermSelection){

}
