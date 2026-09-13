import { $div, assert, fetchText, msg, MyError } from "@i18n";
import { App, Parser, renderKatexSub, Term, Variable } from "@parser";
import { Formula, MathLib, mathLib, Proof, Theorem, VarDecl } from "./formula";
import { DummyStep, FormulaMenuEntry, makeAccordion, putStr, putTex, saveData } from "./algebra_util";
import { makeFormulaDiv } from "./ProofStep";

function splitKeyword(line : string) : [string, string] {
    const k = line.indexOf(" ");
    if(k == -1){
        return [line, ""];
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

export const formulaMenuItems: FormulaMenuEntry[] = [
    {
        type: "submenu",
        name: "交換法則",
        items: [
            {
                type: "action",
                step : new DummyStep(),
                name: "加法",
                latex: "b+a",
            },
            {
                type: "action",
                step : new DummyStep(),
                name: "乗法",
                latex: "ba",
            },
        ],
    },

    {
        type: "submenu",
        name: "展開",
        items: [
            {
                type: "action",
                step : new DummyStep(),
                name: "分配法則",
                latex: "ab+ac",
            },
            {
                type: "action",
                step : new DummyStep(),
                name: "平方差",
                latex: "(a+b)(a-b)",
            },
        ],
    },

    {
        type: "action",
        step : new DummyStep(),
        name: "簡約",
        latex: "a",
    },
];

let comments : string[] = [];

function readProof(lines:string[], proof : Proof){
    const proofContent = makeAccordion(proof.formula.theorem.theoremDiv, `proof`);

    while(lines.length != 0){
        const line = lines.shift()!;
        if(line == ""){
            continue;
        }
        else if(line.startsWith("//")){
            msg(`comment:[${line}]`)
            continue;
        }

        const [keyword, name] = splitKeyword(line);
        if(keyword == "@"){
            // msg(`apply:[${line}]`)

            proof.stepProof(proofContent!, line);
        }
        else if(keyword == "qed"){

            return;
        }
    }
}

function readFormula(lines:string[], formula : Formula){
    while(lines.length != 0){
        const line = lines.shift()!;
        if(line == ""){
            continue;
        }
        else if(line.startsWith("//")){
            msg(`comment:[${line}]`);
            comments.push(line);
            continue;
        }

        if(line == "proof"){

            const proof = formula.startProof();

            putTex(formula.theorem.theoremDiv, formula.predicate);

            readProof(lines, proof);
        }
        else{
            lines.unshift(line);
            return;
        }
    }
}

function readVarDecl(theorem:Theorem, keyword: string, line: string){
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

    const varDecl = new VarDecl(keyword);
    theorem.varDecls.push(varDecl);

    for(const id of refVars){
        const va = new Variable(id.name, type, init);
        id.refVar = va;
        varDecl.vars.push(va);
    }

    const vars = varDecl.vars.map(x => `${x}`).join(", ");
    msg(`${keyword}:[${vars}]`);

}

function readTheorem(lines:string[], theorem : Theorem){
    assert(!mathLib.theorems.has(theorem.name));
    mathLib.theorems.set(theorem.name, theorem);

    while(lines.length != 0){
        const line = lines.shift()!;
        if(line == ""){
            continue;
        }
        else if(line.startsWith("//")){
            msg(`comment:[${line}]`)
            comments.push(line);
            continue;
        }

        const [keyword, name] = splitKeyword(line);

        if(keyword == "let" || keyword == "param"){
            // msg(`let:[${line}]`);

            readVarDecl(theorem, keyword, line);
        }
        else if(line.match(/^[0-9]+:.+$/)){
            const match = line.match(/^([0-9]+):(.+)$/) as RegExpMatchArray;
            const tag   = match[1];
            const predicate = parseExpression(match[2]);

            const formulaDiv = document.createElement("div");
            const formula = new Formula(theorem, tag, predicate, formulaDiv);
            theorem.addFormula(tag, formula);

            makeFormulaDiv(formulaDiv, formula);

            theorem.theoremDiv.appendChild(formulaDiv);

            readFormula(lines, formula);
        }
        else if(keyword == "theorem" || keyword == "law" || keyword == "formula"){
            lines.unshift(line);
            return;
        }
    }
}

export function parseMathFile(text: string) {
    mathLib.clear();

    const lines = text.replaceAll("\r", "").split('\n').map(x => x.trim());

    comments = [];
    while(lines.length != 0){
        const line = lines.shift()!;
        if(line == ""){
            continue;
        }
        else if(line.startsWith("//")){
            msg(`comment:[${line}]`);
            comments.push(line);
            continue;
        }

        const [keyword, name] = splitKeyword(line);
        if(keyword == "namespace"){
            mathLib.name = line.slice(9).trim();
            msg(`namespace:[${mathLib.name}]`);
        }
        else if(line == "axiom"){
        }
        else if(line == "definition"){
        }
        else{
            if(keyword == "theorem" || keyword == "law" || keyword == "formula"){
                msg(`${keyword}:[${name}]`);
                const theorem = new Theorem(comments, keyword, name);
                comments = [];

                readTheorem(lines, theorem);
            }
            else{
                throw new MyError();
            }
        }
    }
}

export async function testProof(){
    const text = await fetchText("./formula/example.math");
    // msg(`proof:[${text}]`);
    parseMathFile(text);

    await saveData("output.math", mathLib.toString());


    // const text2 = await fetchText("./output/output.math");
    // console.log(text2);
    // parseMathFile(text2);
    // await saveData("output2.math", mathLib.toString());

    return true;
}
