import { assert, msg, fetchText } from "@i18n";
import { RefVar, App, parseMath, Term, ConstNum, Path, isLetter, Variable } from "@parser";
import { allTerms } from "./algebra_util.js";

class FormulaError extends Error {    
}

export class Theorem {
    name : string;
    vars : Variable[] = [];
    params : Variable[] = [];
    formulas : Map<string, App> = new Map<string, App>();

    constructor(name : string){
        this.name = name;
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



export function matchFormula(focus : Term, theorem:Theorem, formula: App, sideIdx : number) : Term | undefined {
    assert(formula.isEq());
    const side = formula.args[sideIdx];
    if(focus instanceof App && side instanceof App){
        if(focus.fncName == side.fncName && focus.args.length == side.args.length){

            const [formula_cp, sideL_cp] = side.cloneRoot() as [App, App];

            const dic = new Map<string, Term>();
            const fdic = new Map<string, [App, Term]>();

            for(const param of theorem.params){
                dic.set(param.name, param.init!);
            }
            try{
                matchTerm(dic, fdic, focus, focus, sideL_cp);

                substByDic(dic, fdic, formula_cp);
                msg(`form : OK ${focus} F:${formula_cp}`);

                // const [focusRoot_cp, focus_cp] = focus.cloneRoot() as [App, App];
                // focus_cp.replaceTerm(formula_cp.args[1]);

                return formula_cp.rightSide();
            }
            catch(e){
                if(e instanceof FormulaError){

                    msg(`form : NG ${focus.str()}`);
                }
                else{
                    assert(false);
                }
            }
        }
    }

    return undefined;
}

function enumFormulasForTermSelection(sel : TermSelection){

}

function enumFormulasForEquation(sel : TermSelection){

}

function enumFormulasForTerm(sel : TermSelection){

}

function enumFormulasForTerms(sel : TermSelection){

}
