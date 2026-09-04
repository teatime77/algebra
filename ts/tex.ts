import { $, $div, MyError } from "@i18n";
import { App, ConstNum, parseMath, RefVar, setIsProof, Term } from "@parser";
import katex from "katex";
// KaTeX ships its stylesheet without TypeScript declarations.
// @ts-ignore -- this is a runtime-only side-effect import.
import "katex/dist/katex.min.css";

interface NodeSelection {
    kind: "node";
    nodeId: string;
}

interface AssociativeRangeSelection {
    kind: "associative-range";

    parentId: string;

    startIndex: number;
    endIndex: number;
}

type MathSelection = | NodeSelection | AssociativeRangeSelection;

interface SelectionCandidate {
    selection: MathSelection;
    area: number;
}

function findAssociativeSelection(container: HTMLElement, mouse_rect: DOMRect): SelectionCandidate | null {
    /*
     * Immediate children of associative nodes.
     */
    const elements =
        Array.from(
            container.querySelectorAll<HTMLElement>(
                ".katex-html " +
                "[data-assocparent]" +
                "[data-associndex]"
            )
        );


    /*
     * Group fully-contained operands by parent.
     *
     * For example:
     *
     *     parent n1 -> [1, 2, 3]
     */
    const groups = new Map<string, Map<number, HTMLElement>>();

    for (const element of elements) {
        const rect = element.getBoundingClientRect();

        /*
         * Same strict containment rule as
         * findNodeSelection().
         */

        if (!containsRectangle(mouse_rect, rect) ) {
            continue;
        }

        const parent_id  = element.dataset.assocparent;
        const index_text = element.dataset.associndex;


        if (parent_id === undefined || index_text === undefined) {
            continue;
        }

        const index = Number(index_text);

        if (!Number.isInteger(index))
            continue;

        let group = groups.get(parent_id);

        if (!group) {

            group = new Map<number, HTMLElement>();

            groups.set(parent_id, group);
        }

        group.set(index, element);
    }


    let best: SelectionCandidate | null = null;

    /*
     * Look for consecutive runs.
     */
    for (const [parent_id, group] of groups) {

        const indexes = Array.from(group.keys() ).sort(
                (a, b) => a - b
            );


        if (indexes.length < 2)
            continue;


        /*
         * Example:
         *
         * indexes = [0, 1, 3, 4, 5]
         *
         * creates:
         *
         * [0,1]
         * [3,4,5]
         */

        let start_index = indexes[0];
        let end_index   =   indexes[0];

        function considerRange(start: number, end: number): void {
            /*
             * At least two operands are required.
             */

            if (end <= start) {
                return;
            }

            const rectangles: DOMRect[] = [];

            for (let index = start; index <= end; ++index) {
                const element = group.get(index);
                if (!element)
                    return;

                rectangles.push( element.getBoundingClientRect() );
            }

            /*
             * Find a bounding rectangle for the
             * entire associative range.
             */

            let left   = rectangles[0].left;
            let right  = rectangles[0].right;
            let top    = rectangles[0].top;
            let bottom = rectangles[0].bottom;


            for (let i = 1; i < rectangles.length; ++i) {
                const rect = rectangles[i];

                left  = Math.min(left, rect.left);
                right = Math.max(right, rect.right);

                top    = Math.min(top, rect.top);
                bottom = Math.max(bottom, rect.bottom);
            }

            const area = (right - left) * (bottom - top);

            /*
             * If nested associative operations both
             * qualify, use the visually largest range.
             */
            if (best === null || area > best.area) {
                best = {
                    selection: {
                        kind: "associative-range",
                        parentId: parent_id,
                        startIndex: start,
                        endIndex: end
                    },

                    area
                };
            }
        }

        for (let i = 1; i < indexes.length; ++i) {
            const current = indexes[i];

            if (current === end_index + 1) {
                end_index = current;

                continue;
            }

            /*
             * Previous contiguous range ended.
             */
            considerRange(start_index, end_index);

            start_index = current;
            end_index   = current;
        }

        /*
         * Last range.
         */
        considerRange(start_index, end_index);
    }

    return best;
}


/*
 * Values inserted into data attributes are generated
 * internally, but validate them anyway.
 */

function validateDataValue(
    value: string
): string {

    if ( !/^[A-Za-z0-9_-]+$/.test( value) ) {

        throw new Error( `Invalid htmlData value: ${value}` );
    }

    return value;
}


function htmlData(attributes: Record<string, string | number>, body: string): string {

    const attributes_text = Object.entries(attributes)
            .map( ([name, value]) => `${name}=${validateDataValue(String(value))}` )
            .join(",");

    return (`\\htmlData{${attributes_text}}{${body}}`);
}

/* ============================================================
 * Mouse rectangle
 * ============================================================
 */

function makeRectangle( x1: number, y1: number, x2: number, y2: number): DOMRect {
    const left = Math.min( x1, x2);
    const top  = Math.min( y1, y2);

    const width = Math.abs( x2 - x1);
    const height = Math.abs( y2 - y1);

    return new DOMRect( 
        left, 
        top, 
        width, 
        height
    );
}


/* ============================================================
 * Rectangle containment
 *
 * Is "inner" completely contained in "outer"?
 * ============================================================
 */

function containsRectangle(outer: DOMRect, inner: DOMRect): boolean {
    return (
        inner.left >= outer.left &&
        inner.right <= outer.right &&
        inner.top >= outer.top &&
        inner.bottom <= outer.bottom
    );
}


/* ============================================================
 * Node selection
 *
 * THIS IS THE COMPLETE SELECTION ALGORITHM.
 *
 * 1. Find every [data-astid].
 *
 * 2. Get its bounding rectangle.
 *
 * 3. Check whether the entire node rectangle is
 *    contained in the mouse rectangle.
 *
 * 4. Of all contained nodes, choose the one with
 *    the largest area.
 *
 * No:
 *
 *     center-point tests
 *     coverage
 *     scores
 *     anchor nodes
 *     ancestor expansion
 *     associative selection
 *
 * ============================================================
 */

function findNodeSelection( 
    container: HTMLElement, 
    mouse_rect: DOMRect
): SelectionCandidate | null {

    const elements = container.querySelectorAll<HTMLElement>( 
            ".katex-html [data-astid]" 
        );

    let best: SelectionCandidate | null = null;


    for (const element of elements) {
        const ast_id = element.dataset.astid;

        if (!ast_id) 
            continue;


        const rect = element.getBoundingClientRect();

        if ( rect.width <= 0 || rect.height <= 0 ) {
            continue;
        }


        if ( !containsRectangle( mouse_rect, rect) ) {
            continue;
        }

        const area = rect.width * rect.height;

        if ( best === null || area > best.area) {

            best = {
                selection: {
                    kind: "node",
                    nodeId: ast_id
                },

                area
            };
        }
    }

    return best;
}

function findSelection( container: HTMLElement, mouse_rect: DOMRect): MathSelection | null {
    const node_candidate = findNodeSelection( container, mouse_rect);

    const associative_candidate = findAssociativeSelection( container, mouse_rect);

    if ( node_candidate === null && associative_candidate === null) {
        return null;
    }


    if ( node_candidate === null) {
        return ( associative_candidate! .selection);
    }


    if ( associative_candidate === null) {
        return ( node_candidate.selection);
    }


    /*
     * Both are possible.
     *
     * Choose the larger mathematical region.
     */

    if ( associative_candidate.area > node_candidate.area) {
        return ( associative_candidate.selection);
    }


    return ( node_candidate.selection);
}

/* ============================================================
 * Find rendered DOM element for AST node
 * ============================================================
 */

function findAstElement( container: HTMLElement, ast_id: string): HTMLElement | null {

    const elements = container.querySelectorAll<HTMLElement>( ".katex-html [data-astid]" );

    for (const element of elements) {
        if ( element.dataset.astid === ast_id) {

            return element;
        }
    }

    return null;
}


/* ============================================================
 * Highlight
 * ============================================================
 */

function clearHighlight( container: HTMLElement): void {
    container.querySelectorAll( 
            ".ast-selected" 
        )
        .forEach(
            element => {
                element.classList.remove( "ast-selected" );
            }
        );
}


function highlightSelection( container: HTMLElement, selection: MathSelection | null): void {

    clearHighlight(container);

    if (!selection)
        return;

    /* ========================================================
     * Ordinary AST node
     * ========================================================
     */

    if (selection.kind === "node") {
        const element = findAstElement(container, selection.nodeId);

        element?.classList.add("ast-selected");

        return;
    }


    /* ========================================================
     * Associative operands
     * ========================================================
     */

    const operands = container.querySelectorAll<HTMLElement>(
            ".katex-html " +
            "[data-assocparent]" +
            "[data-associndex]"
        );


    for (const element of operands) {

        if ( element.dataset.assocparent !== selection.parentId) {
            continue;
        }


        const index = Number( element.dataset.associndex);

        if ( index >= selection.startIndex && 
            index <= selection.endIndex) {

            element.classList.add( "ast-selected" );
        }
    }


    /* ========================================================
     * Operators between selected operands
     *
     * If terms 1..3 are selected:
     *
     *     term1 + term2 + term3
     *
     * separators 1 and 2 are highlighted.
     * ========================================================
     */

    const separators = 
        container.querySelectorAll<HTMLElement>( 
            ".katex-html " + 
            "[data-assocsep]" + 
            "[data-sepindex]" 
        );


    for (const element of separators) {

        if ( element.dataset.assocsep !== selection.parentId) {
            continue;
        }


        const index = Number( element.dataset.sepindex);

        if ( index >= selection.startIndex && 
            index < selection.endIndex) {

            element.classList.add( "ast-selected" );
        }
    }
}


/* ============================================================
 * Create page
 * ============================================================
 */

const math_container = $div("math-container");

const result = $("result-pre") as HTMLPreElement;

const selection_box = document.createElement( "div" );

selection_box.className = "selection-box";

document.body.appendChild( selection_box);


/* ============================================================
 * Render KaTeX
 * ============================================================
 */

function myLatex(){
    setIsProof(true);
    const s= `
        limit(
            integrate(
                sqrt(1 + t^2) / (1 + t/(1+t*2+x)),
                t, 0, 1
            )
            /
            root(
                (1 + x^2) / (1 + x),
                3
            )
            , x, 0
        )
    `

    const expr = parseMath(s.replaceAll("\n", " "));

    return toTex(expr);
}

const latex = myLatex();

console.log( latex);

katex.render(
    latex,
    math_container,
    {
        throwOnError: true,

        displayMode: true,

        trust: context => context.command === "\\htmlData",

        strict: error_code => error_code === "htmlExtension" ? "ignore" : "warn" 
    }
);


/* ============================================================
 * Pointer interaction
 * ============================================================
 */

let dragging = false;

let pointer_id: number | null = null;

let start_x = 0;
let start_y = 0;


function showSelectionBox( rect: DOMRect): void {

    selection_box.style.display = "block";

    selection_box.style.left = `${rect.left}px`;

    selection_box.style.top = `${rect.top}px`;

    selection_box.style.width = `${rect.width}px`;

    selection_box.style.height = `${rect.height}px`;
}


function hideSelectionBox(): void {
    selection_box.style.display = "none";
}


/*
 * Called continuously while dragging.
 */

function updateSelection( current_x: number, current_y: number): void {
    const mouse_rect = makeRectangle( start_x, start_y, current_x, current_y);

    showSelectionBox( mouse_rect);

    /*
     * Ignore tiny accidental movements.
     */

    if ( mouse_rect.width < 2 || mouse_rect.height < 2 ) {
        clearHighlight( math_container);

        result.textContent = "";

        return;
    }

    const selection = findSelection( math_container, mouse_rect);

    highlightSelection( math_container, selection);
}


/* ============================================================
 * pointerdown
 * ============================================================
 */

math_container.addEventListener("pointerdown",
    event => {
        if (event.button !== 0) {
            return;
        }

        event.preventDefault();

        dragging = true;
        pointer_id = event.pointerId;

        start_x = event.clientX;
        start_y = event.clientY;

        /*
         * Clear previous selection when
         * starting a new drag.
         */

        clearHighlight(math_container);

        result.textContent = "";

        /*
         * Keep receiving pointermove even if
         * pointer leaves the math container.
         */

        math_container.setPointerCapture( event.pointerId);


        showSelectionBox( 
            makeRectangle( start_x, start_y, start_x, start_y) 
        );
    }
);


/* ============================================================
 * pointermove
 * ============================================================
 */

math_container.addEventListener("pointermove",
    event => {
        if (!dragging || event.pointerId !== pointer_id) {
            return;
        }

        updateSelection(event.clientX, event.clientY);
    }
);


/* ============================================================ 
 * pointerup
 * ============================================================
 */ 

math_container.addEventListener("pointerup", 
    event => { 

        if ( !dragging || event.pointerId !== pointer_id) { 
            return; 
        } 

        /* 
         * Final calculation. 
         */

        updateSelection( event.clientX, event.clientY);

        dragging = false;

        hideSelectionBox();


        if ( math_container.hasPointerCapture(event.pointerId)) {

            math_container.releasePointerCapture(event.pointerId);
        }

        pointer_id = null;
    }
);


/* ============================================================
 * pointercancel
 * ============================================================
 */

math_container.addEventListener(
    "pointercancel",

    event => {

        if ( event.pointerId !== pointer_id) {
            return;
        }


        dragging = false;

        pointer_id = null;


        hideSelectionBox();
    }
);

function nodeId(term:Term) : string {
    return `nd${term.id}`;
}

function toTex(term : Term) : string {
    let body: string;

    if(term instanceof ConstNum){
        body = ` ${term.text} `;
    }
    else if(term instanceof RefVar){
        body = ` ${term.name} `;
    }
    else if(term instanceof App){
        const args = term.args.map(x => toTex(x));

        switch(term.fncName){
        case "limit":
            body =
                `\\displaystyle ` +
                `\\lim_{${args[1]}` +
                `\\to${args[2]}} ` +
                `${args[0]}`;
            break;

        case "integrate":
            body =
                `\\displaystyle ` +
                `\\int_{${args[2]}}` +
                `^{${args[3]}} ` +
                `${args[0]}` +
                `\\,d${args[1]}`;
            break;

        case "sqrt":
            body = `\\sqrt{${args[0]}}`;
            break;

        case "root":
            body = `\\sqrt[${args[1]}]{${args[0]}}`;
            break;

        case "+":
            body = args.join(" + ");
            break;

        case "*":
            body = args.join(" \\cdot ");
            break;

        case "/":
            body = `\\frac{${args[0]}}{${args[1]}}`;
            break;

        case "^":
            body = `{${args[0]}}^{${args[1]}}`;
            break;

        default:
            throw new MyError();
        }

        if(term.isOperator() && term.parent != null && term.parent.isOperator() && !term.parent.isDiv()){
            if(term.parent.precedence() <= term.precedence()){
                body = `\\left(${body}\\right)`;
            }            
        }
    }
    else{
        throw new MyError();
    }

    const attributes: Record<string, string | number> = {
        astid: `nd${nodeId(term)}`
    };

    if(term.parent instanceof App && ["+", "*"].includes(term.parent.fncName)){
        attributes.assocparent = nodeId(term.parent);
        attributes.associndex = term.argIdx();

    }

    return htmlData(attributes, body);
}

export function initTexTest(){
}