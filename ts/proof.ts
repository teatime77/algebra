import { $div, assert, fetchText, msg, MyError } from "@i18n";
import { App, ConstNum, Parser, RefVar, renderKatexSub, Term, Variable } from "@parser";
import { matchFormula, Theorem } from "./formula";
import { allTerms, setHashTerm2 } from "./algebra_util";

const theorems : Map<string, Theorem> = new Map<string, Theorem>();

let prevTheorem : Theorem;

function isExpressionNumber(term : Term) : term is App {
    return term instanceof App && term.fncName == "." && term.args[0] instanceof RefVar && term.args[0].name.startsWith("#");
}

function putStr(s : string){
    const p = document.createElement("p");
    p.innerHTML = s;
    $div("proof-div").appendChild(p);
}

function putTex(term : Term){
    const p = document.createElement("p");
    // p.innerHTML = `$$\n${term.tex()}\n$$`;
    $div("proof-div").appendChild(p);
    renderKatexSub(p, term.tex());
}

function getFormula(app: App) : [Theorem, App, number] {
    assert(app.fncName == "." && app.args.length <= 3 && app.args.every(x => x instanceof RefVar));
    const names = (app.args as RefVar[]).map(x => x.name);
    const theorem = theorems.get(names[0]);
    if(theorem == undefined){
        throw new MyError();
    }

    const formula = theorem.formulas.get(names[1]);
    if(formula == undefined){
        throw new MyError();
    }

    if(app.args.length == 2){

        return [theorem, formula, 0];
    }

    const sideName = (app.args[2] as RefVar).name;
    switch(sideName){
    case "L": return [theorem, formula, 0];
    case "R": return [theorem, formula, formula.args.length - 1];
    }

    const sideIdx = parseInt(sideName) - 1;
    assert(0 <= sideIdx && sideIdx <= formula.args.length - 1);

    return [theorem, formula, sideIdx];
}

function splitKeyword(line : string) : [string, string] {
    const k = line.indexOf(" ");
    if(k == -1){
        return ["", line];
    }
    const keyword = line.slice(0, k);
    const data = line.slice(k + 1).trim();

    return [keyword, data];
}

function parseExpression(tag:string, data:string) : App {
    msg(`expr:[${tag}][${data}]`);

    if(prevTheorem == undefined || prevTheorem.formulas.has(tag)){
        throw new MyError();
    }
    const parser = new Parser(data);
    const term = parser.RootExpression();
    if(!(term instanceof App)){
        throw new MyError();
    }
    prevTheorem.formulas.set(tag, term);
    msg(`expr:[${term}]`);

    return term;
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

export function parseProof(text: string) {
    const lines = text.replaceAll("\r", "").split('\n').map(x => x.trim());

    let prevExpr : Term | undefined;

    for(const line of lines){
        if(line == ""){
            continue;
        }
        else if(line == "proof"){
            putTex(prevExpr!);
            putStr("proof");
        }
        else if(line == "qed"){
        }
        else if(line == "axiom"){
        }
        else if(line == "definition"){
        }
        else if(line.startsWith("//")){
            msg(`comment:[${line}]`)
        }
        else if(line.match(/^[0-9]+:.+$/)){
            const match = line.match(/^([0-9]+):(.+)$/) as RegExpMatchArray;
            prevExpr = parseExpression(match[1], match[2]);
        }
        else{
            const [keyword, name] = splitKeyword(line);
            if(keyword == "@"){
                // msg(`apply:[${line}]`)
                if(!(prevExpr instanceof App)){
                    throw new MyError();
                }

                const parser = new Parser(line.slice(1));
                const terms:Term[] = [];
                parser.readList(terms);
                const s = terms.map(x => x.toString()).join(", ");

                const formulaPath = terms.shift();
                assert(formulaPath instanceof App);

                const [theorem, formula, sideIdx] = getFormula(formulaPath as App);
                for(const param of theorem.params){
                    assert(terms.length != 0);
                    const term = terms.shift()!;
                    param.init = term;
                }

                let target : Term;

                let root : Term;
                if(terms.length == 0){

                    target = prevExpr.clone();
                    root   = target;
                }
                else{

                    target = getTermInApply(prevExpr, terms.shift()!).clone();

                    if(terms.length == 0){

                        root = prevExpr.clone();
                    }
                    else{

                        root = getTermInApply(prevExpr, terms.shift()!).clone();
                                                
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

                const formula_R = matchFormula(target, theorem, formula, sideIdx)!;
                assert(formula_R != undefined);

                if(target == root){
                    root = formula_R;
                }
                else{

                    target.replaceTerm(formula_R);
                }

                putStr(line);
                putTex(root);

                prevExpr = root;

                msg(`apply:[${prevExpr}]`);
            }
            else if(keyword == "namespace"){
                msg(`namespace:[${line.slice(9).trim()}]`);
            }
            else if(keyword == "theorem" || keyword == "law" || keyword == "formula"){
                prevTheorem = new Theorem(name);

                assert(!theorems.has(name));
                theorems.set(name, prevTheorem);
                msg(`${keyword}:[${name}]`);
            }
            else if(keyword == "let" || keyword == "param"){
                if(prevTheorem == undefined){
                    throw new MyError();
                }
                // msg(`let:[${line}]`);

                const parser = new Parser(line);
                parser.nextToken(keyword);
                const refVars = parser.readIds();

                let type : Term | undefined;
                let init : Term | undefined;

                if(parser.current() == ":"){
                    parser.nextToken(":");
                    type = parser.ArithmeticExpression();
                }

                if(parser.current() == "="){
                    parser.nextToken("=");
                    init = parser.ArithmeticExpression();
                }

                for(const id of refVars){
                    const va = new Variable(id.name, type, init);
                    id.refVar = va;
                    if(keyword == "let"){
                        prevTheorem.vars.push(va);
                    }
                    else{
                        prevTheorem.params.push(va);
                    }
                }

                const vars = prevTheorem.vars.map(x => `${x}`).join(", ");
                msg(`${keyword}:[${vars}]`);
            }
            else if(keyword == "formula"){
            }
            else{
                throw new MyError();
            }
        }
    }

    
    // // msg(`parse-Math:[${text}]`);
    // const parser = new Parser(text);
    // const trm = parser.RootExpression();
    // if(parser.token.typeTkn != TokenType.eot){
    //     throw new MyError();
    // }

    // trm.setParent(null);
}

export async function testProof(){
    const text = await fetchText("./formula/example.math");
    // msg(`proof:[${text}]`);
    parseProof(text);

    return true;
}
