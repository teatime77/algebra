import { assert, MyError, Speech, msg, fetchText, $div } from "@i18n";
import { App, ConstNum, operator, parseMath, Rational, RefVar, renderKatexSub, setIsProof, Term } from "@parser";
import { simplify } from "./simplifier.js";
import { testProof } from "./proof.js";
import { initTexTest } from "./tex.js";

import katex from "katex";

export function putStr(div:HTMLDivElement, s : string){
    const p = document.createElement("p");
    p.innerHTML = s;
    div.appendChild(p);
}

export function putTex(div:HTMLDivElement, term : Term){
    const p = document.createElement("p");
    // p.innerHTML = `$$\n${term.tex()}\n$$`;
    div.appendChild(p);
    renderKatexSub(p, term.tex());
}

export function makeAdd(trms : Term[]) : App {
    return new App(operator("+"), trms.slice());
}

export function makeMul(trms : Term[]) : App {
    return new App(operator("*"), trms.slice());
}

export function makeDiv(trms : Term[]) : App {
    return new App(operator("/"), trms.slice());
}

export function makeEq(trms : Term[]) : App {
    return new App(operator("=="), trms.slice());
}


export function makeAccordion(parent:HTMLElement, title:string) : HTMLDivElement {
    const details = document.createElement("details");
    const summary = document.createElement("summary");
    const content = document.createElement("div");

    details.className = "accordion";

    summary.textContent= title;

    content.className = "accordion-content";

    details.appendChild(summary);
    details.appendChild(content);

    parent.appendChild(details);

    return content;
}
export function getAllTerms(t : Term, terms: Term[]){
    terms.push(t);

    if(t instanceof App){
        assert(t.fnc != null, "get all terms");
        getAllTerms(t.fnc, terms);

        t.args.forEach(x => getAllTerms(x, terms));
    }
}

export function allTerms(trm : Term) : Term[] {
    const terms : Term[] = [];
    getAllTerms(trm, terms);

    return terms;
}

function fastHashToBigInt(str: string): bigint {
    let hash = 0xcbf29ce484222325n; // 64-bit FNV offset basis
    const prime = 0x100000001b3n;   // 64-bit FNV prime

    for (let i = 0; i < str.length; i++) {
        hash ^= BigInt(str.charCodeAt(i));

        // Multiply by prime and constrain to 64-bit unsigned integer
        hash = BigInt.asUintN(64, hash * prime);
    }

    return hash;
}


let hashMap : Map<string, bigint> ;

export function initHashTerm(){
    hashMap = new Map<string, bigint>();
}

function hashText(positions : number[], text : string) : bigint {
    const key = `${positions.join(".")}:${text}`
    let value = hashMap.get(key);
    if(value == undefined){
        if(hashMap.size < 64){

            value = 2n ** BigInt(hashMap.size);
        }
        else{

            value = BigInt(Math.random() * (2 ** 50));
        }
        // msg(`hash ${value.toString(2)} ${key}`);
        hashMap.set(key, value);
    }

    return value;
}

function hashRational(r : Rational) : string {
    if(r.denominator == 1){
        if(r.numerator == 1){
            return "";
        }
        else{
            return `${r.numerator}:`;
        }
    }
    else{
        return `${r.numerator}/${r.denominator}:`;
    }
}


export function setHashTerm(positions : number[], term : Term) : bigint {
    let hash : bigint;

    let value_str : string;
    if(positions.length == 0){
        value_str = "";
    }
    else{
        value_str = hashRational(term.value);
    }
    
    if(term instanceof ConstNum){

        hash = hashText(positions, value_str);
    }
    else if(term instanceof RefVar){
        hash = hashText(positions, value_str + term.name);
    }
    else if(term instanceof App){
        hash = hashText(positions, value_str + term.fncName);

        const positions_cp = positions.slice();
        if(term.isAdd() || term.isMul()){
            positions_cp.push(0);
            term.args.forEach(x => hash += setHashTerm(positions_cp, x));
        }
        else{
            for(const [idx, arg] of term.args.entries()){
                positions_cp.push(idx);

                hash += setHashTerm(positions_cp, arg);

                positions_cp.pop();
            }
        }
        
    }
    else{
        throw new MyError();
    }

    term.hash = hash;
    return term.hash;
}


export function setHashTerm2(term : Term){   
    const value_str = `${term.value}`;
    let term_str : string = "";
    
    if(term instanceof RefVar){
        term_str = term.name;
    }
    else if(term instanceof App){
        term.args.forEach(x => setHashTerm2(x));
        const args_str = term.args.map(x => x.hash2).join(",");
        term_str = `${term.fncName}:[${args_str}]`;
    }

    term.hash2 = `<${term.constructor.name}:${value_str}:${term_str}>`;
    term.hash = fastHashToBigInt(term.hash2);
}

function getTermByPointerEvent(map : Map<number,Term>, ev : PointerEvent) : Term {
    let target : HTMLElement = ev.target as HTMLElement;
    for(; target != null; target = target.parentElement as HTMLElement){
        if(target.id.startsWith("tex-term-")){

            const id_offset = "tex-term-".length;
            const id = parseInt(target.id.substring(id_offset));
            const term = map.get(id)!;
            assert(term != undefined);
            return term;
        }
    }

    throw new MyError();
}

export async function initAlgebra(){
    setIsProof(true);
    initTexTest();
    await testProof();

    const pre = document.getElementById("eqs") as HTMLPreElement;
    const text = pre.innerText.split("\n");
    const eqs  = text.map(x => x.trim()).filter(x => x != "")

    const speech = new Speech();
    // setPlayMode(PlayMode.fastForward);
    for(const eq of eqs){
        const term = parseMath(eq);

        const span = document.createElement("span");
        span.style.height = "30px";
        span.style.cursor = "default";
        span.style.userSelect = "none";
    
        document.body.appendChild(span);
    
        await simplify(speech, span, term);

        const hr = document.createElement("hr");
        document.body.appendChild(hr);
    }

    msg("algebra OK");
}

export interface FormulaMenuItem {
    id : string
    name: string;
    latex: string;
}

export function showFormulaMenu(items: FormulaMenuItem[], x: number, y: number, on_select: (item: FormulaMenuItem) => void): void {
    // すでに開いているメニューがあれば閉じる
    document.querySelector(".formula-popup-menu")?.remove();

    const menu = document.createElement("div");
    menu.className = "formula-popup-menu";

    for (const item of items) {
        const button = document.createElement("button");
        button.type = "button";
        button.className = "formula-popup-item";

        const name = document.createElement("span");
        name.className = "formula-popup-name";
        name.textContent = item.name;

        const formula = document.createElement("span");
        formula.className = "formula-popup-formula";

        katex.render(item.latex, formula, {
            throwOnError: false,
            displayMode: false,
        });

        button.append(name, formula);

        button.addEventListener("click", () => {
            close();

            // メニューを閉じてから数式処理を実行
            on_select(item);
        });

        menu.appendChild(button);
    }

    document.body.appendChild(menu);

    // いったん配置してサイズを取得する
    menu.style.left = `${x}px`;
    menu.style.top = `${y}px`;

    // 画面外にはみ出さないように補正
    const rect = menu.getBoundingClientRect();

    let menu_x = x;
    let menu_y = y;

    if (window.innerWidth < rect.right) {
        menu_x = Math.max(0, window.innerWidth - rect.width);
    }

    if (window.innerHeight < rect.bottom) {
        menu_y = Math.max(0, window.innerHeight - rect.height);
    }

    menu.style.left = `${menu_x}px`;
    menu.style.top  = `${menu_y}px`;

    function close(): void {
        menu.remove();

        document.removeEventListener("pointerdown", handleOutsideClick);
        document.removeEventListener("keydown", handleKeyDown);
    }

    function handleOutsideClick(event: PointerEvent): void {
        if (!menu.contains(event.target as Node)) {
            close();
        }
    }

    function handleKeyDown(event: KeyboardEvent): void {
        if (event.key === "Escape") {
            close();
        }
    }

    // 現在のクリックで即座に閉じないよう、次のイベントループで登録
    setTimeout(() => {
        document.addEventListener("pointerdown", handleOutsideClick);
        document.addEventListener("keydown", handleKeyDown);
    });
}