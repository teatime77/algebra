import { $div, assert, fetchText, msg, MyError } from "@i18n";
import { App, Parser, renderKatexSub, Term, Variable } from "@parser";
import { Formula, Theorem, theorems } from "./formula";
import { FormulaMenuItem, makeAccordion, putStr, putTex, showFormulaMenu } from "./algebra_util";

function splitKeyword(line : string) : [string, string] {
    const k = line.indexOf(" ");
    if(k == -1){
        return ["", line];
    }
    const keyword = line.slice(0, k);
    const data = line.slice(k + 1).trim();

    return [keyword, data];
}

function parseExpression(data:string) : App {
    const parser = new Parser(data);
    const term = parser.RootExpression();
    if(!(term instanceof App)){
        throw new MyError();
    }

    msg(`expr:[${term}]`);

    return term;
}

export function parseProof(text: string) {
    const lines = text.replaceAll("\r", "").split('\n').map(x => x.trim());

    let prevTheorem : Theorem | undefined;
    let proofContent : HTMLDivElement | undefined;
    let theoremDiv  : HTMLDivElement | undefined;

    for(const line of lines){
        if(line == ""){
            continue;
        }
        else if(line == "proof"){
            if(prevTheorem == undefined || theoremDiv == undefined){
                throw new MyError();
            }

            prevTheorem.lastFormula().startProof();

            putTex(theoremDiv, prevTheorem.lastFormula().predicate);

            proofContent = makeAccordion(theoremDiv, `proof`);
        }
        else if(line == "qed"){
            proofContent = undefined;
        }
        else if(line == "axiom"){
        }
        else if(line == "definition"){
        }
        else if(line.startsWith("//")){
            msg(`comment:[${line}]`)
        }
        else if(line.match(/^[0-9]+:.+$/)){
            if(prevTheorem == undefined || theoremDiv == undefined){
                throw new MyError();
            }

            const match = line.match(/^([0-9]+):(.+)$/) as RegExpMatchArray;
            const tag   = match[1];
            const predicate = parseExpression(match[2]);
            const formula = new Formula(predicate);
            prevTheorem.addFormula(tag, formula);

            const formulaDiv = document.createElement("div");

            putStr(formulaDiv, tag);

            const btn = document.createElement("button");
            btn.textContent = "...";
            btn.addEventListener("click", (event:PointerEvent)=>{

                const items: FormulaMenuItem[] = [
                    {
                        id : "1",
                        name: "加法の交換法則",
                        latex: "b+a",
                    },
                    {
                        id : "2",
                        name: "分配法則",
                        latex: "ab+ac",
                    },
                    {
                        id : "3",
                        name: "平方差",
                        latex: "(a+b)(a-b)",
                    },
                ];


                showFormulaMenu(
                    items,
                    event.clientX,
                    event.clientY,
                    (item) => {
                        msg(`selected:${item.name}`);
                    },
                );
            });

            formulaDiv.appendChild(btn);

            putTex(formulaDiv, formula.predicate);

            theoremDiv.appendChild(formulaDiv);
        }
        else{
            const [keyword, name] = splitKeyword(line);
            if(keyword == "@"){
                // msg(`apply:[${line}]`)
                if(prevTheorem == undefined){
                    throw new MyError();
                }

                prevTheorem.lastFormula().lastProof().stepProof(proofContent!, line);
            }
            else if(keyword == "namespace"){
                msg(`namespace:[${line.slice(9).trim()}]`);
            }
            else if(keyword == "theorem" || keyword == "law" || keyword == "formula"){
                prevTheorem = new Theorem(name);

                assert(!theorems.has(name));
                theorems.set(name, prevTheorem);


                theoremDiv = prevTheorem.makeHtml();
                $div("formula-book").appendChild(theoremDiv);



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
