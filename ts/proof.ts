import { assert, fetchText, msg, MyError } from "@i18n";
import { App, ConstNum, Parser, RefVar, Term, Variable } from "@parser";
import { matchFormula } from "./formula";
import { allTerms, setHashTerm2 } from "./algebra_util";

class Theorem {
    name : string;
    vars : Variable[] = [];
    formulas : Map<string, App> = new Map<string, App>();

    constructor(name : string){
        this.name = name;
    }
}

const theorems : Map<string, Theorem> = new Map<string, Theorem>();

let prevTheorem : Theorem;

function isExpressionNumber(term : Term) : term is App {
    return term instanceof App && term.fncName == "." && term.args[0] instanceof RefVar && term.args[0].name.startsWith("#");
}

function getFormula(app: App) : [Theorem, App] {
    assert(app.fncName == "." && app.args.length == 2 && app.args.every(x => x instanceof RefVar));
    const names = (app.args as RefVar[]).map(x => x.name);
    const theorem = theorems.get(names[0]);
    if(theorem == undefined){
        throw new MyError();
    }

    const formula = theorem.formulas.get(names[1]);
    if(formula == undefined){
        throw new MyError();
    }
    
    return [theorem, formula];
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

                const formulaPath = terms.pop();
                assert(formulaPath instanceof App);

                let target : Term;

                let root : Term;
                if(terms.length == 0){

                    target = prevExpr.clone();
                    root   = target;
                }
                else{

                    target = getTermInApply(prevExpr, terms.pop()!).clone();

                    if(terms.length == 0){

                        root = prevExpr.clone();
                    }
                    else{

                        root = getTermInApply(prevExpr, terms.pop()!).clone();
                                                
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

                const [theorem, formula] = getFormula(formulaPath as App);

                const formula_R = matchFormula(target, formula)!;
                assert(formula_R != undefined);

                if(target == root){
                    root = formula_R;
                }
                else{

                    target.replaceTerm(formula_R);
                }

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
            else if(keyword == "let"){
                if(prevTheorem == undefined){
                    throw new MyError();
                }
                // msg(`let:[${line}]`);

                const parser = new Parser(line);
                parser.nextToken("let");
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
                    prevTheorem.vars.push(va);
                }

                const vars = prevTheorem.vars.map(x => `${x}`).join(", ");
                msg(`let:[${vars}]`);
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
