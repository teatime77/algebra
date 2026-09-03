import { $, $div } from "@i18n";
import katex from "katex";
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

interface AssociativePosition {
    parentId: string;
    index: number;
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

/* ============================================================
 * AST definitions
 * ============================================================
 */

interface AstNodeBase {
    id: string;
}

interface NumberNode extends AstNodeBase {
    type: "number";
    value: number;
}

interface VariableNode extends AstNodeBase {
    type: "variable";
    name: string;
}

interface AddNode extends AstNodeBase {
    type: "add";
    terms: AstNode[];
}

interface MultiplyNode extends AstNodeBase {
    type: "multiply";
    factors: AstNode[];
}

interface BinaryNode extends AstNodeBase {
    type: "binary";
    operator: "-" | "/" | "^";
    left: AstNode;
    right: AstNode;
}

interface RootNode extends AstNodeBase {
    type: "root";

    radicand: AstNode;

    /*
     * undefined:
     *
     *     sqrt(x)
     *
     * degree = 3:
     *
     *     cube-root(x)
     */
    degree?: AstNode;
}

interface IntegralNode extends AstNodeBase {
    type: "integral";

    variable: VariableNode;

    lower: AstNode;
    upper: AstNode;

    integrand: AstNode;
}

interface LimitNode extends AstNodeBase {
    type: "limit";

    variable: VariableNode;

    target: AstNode;

    expression: AstNode;
}

type AstNode =
    | NumberNode
    | VariableNode
    | AddNode
    | MultiplyNode
    | BinaryNode
    | RootNode
    | IntegralNode
    | LimitNode;


/* ============================================================
 * Test expression
 *
 *
 *                        sqrt(1 + t^2)
 *              integral ---------------- dt
 *                0..x            t
 *                           1 + -----
 *                               1 + t
 *
 * lim     ---------------------------------
 * x->0                      3
 *                  ( sqrt( (1+x^2)/(1+x) ) )
 *
 *
 * LaTeX:
 *
 *              ∫₀ˣ √(1+t²)/(1+t/(1+t)) dt
 * lim          ---------------------------
 * x→0           (√((1+x²)/(1+x)))³
 *
 * ============================================================
 */

const ast: AstNode = {
    id: "n1",
    type: "limit",

    variable: {
        id: "n2",
        type: "variable",
        name: "x"
    },

    target: {
        id: "n3",
        type: "number",
        value: 0
    },

    expression: {
        id: "n4",
        type: "binary",
        operator: "/",

        /* ====================================================
         * Numerator: integral
         * ====================================================
         */

        left: {
            id: "n5",
            type: "integral",

            variable: {
                id: "n6",
                type: "variable",
                name: "t"
            },

            lower: {
                id: "n7",
                type: "number",
                value: 0
            },

            upper: {
                id: "n8",
                type: "variable",
                name: "x"
            },

            /*
             *
             *          sqrt(1+t²)
             *          -----------
             *              t
             *          1 + -----
             *              1+t
             *
             */

            integrand: {
                id: "n9",
                type: "binary",
                operator: "/",

                /*
                 * sqrt(1+t²)
                 */

                left: {
                    id: "n10",
                    type: "root",

                    radicand: {
                        id: "n11",
                        type: "add",

                        terms: [
                            {
                                id: "n12",
                                type: "number",
                                value: 1
                            },

                            {
                                id: "n13",
                                type: "binary",
                                operator: "^",

                                left: {
                                    id: "n14",
                                    type: "variable",
                                    name: "t"
                                },

                                right: {
                                    id: "n15",
                                    type: "number",
                                    value: 2
                                }
                            }
                        ]
                    }
                },

                /*
                 *
                 *        t
                 *  1 + -----
                 *       1+t
                 *
                 */

                right: {
                    id: "n16",
                    type: "add",

                    terms: [
                        {
                            id: "n17",
                            type: "number",
                            value: 1
                        },

                        {
                            id: "n18",
                            type: "binary",
                            operator: "/",

                            left: {
                                id: "n19",
                                type: "variable",
                                name: "t"
                            },

                            right: {
                                id: "n20",
                                type: "add",

                                terms: [
                                    {
                                        id: "n21",
                                        type: "number",
                                        value: 1
                                    },

                                    {
                                        id: "n22",
                                        type: "variable",
                                        name: "t"
                                    }
                                    ,
                                    {
                                        id: "n23",
                                        type: "number",
                                        value: 2
                                    },

                                    {
                                        id: "n24",
                                        type: "variable",
                                        name: "x"
                                    }
                                ]
                            }
                        }
                    ]
                }
            }
        },

        /* ====================================================
         * Denominator:
         *
         *          1 + x²
         *     sqrt -------
         *          1 + x
         *
         * raised to power 3.
         * ====================================================
         */

        right: {
            id: "n23",
            type: "binary",
            operator: "^",

            left: {
                id: "n24",
                type: "root",

                radicand: {
                    id: "n25",
                    type: "binary",
                    operator: "/",

                    left: {
                        id: "n26",
                        type: "add",

                        terms: [
                            {
                                id: "n27",
                                type: "number",
                                value: 1
                            },

                            {
                                id: "n28",
                                type: "binary",
                                operator: "^",

                                left: {
                                    id: "n29",
                                    type: "variable",
                                    name: "x"
                                },

                                right: {
                                    id: "n30",
                                    type: "number",
                                    value: 2
                                }
                            }
                        ]
                    },

                    right: {
                        id: "n31",
                        type: "add",

                        terms: [
                            {
                                id: "n32",
                                type: "number",
                                value: 1
                            },

                            {
                                id: "n33",
                                type: "variable",
                                name: "x"
                            }
                        ]
                    }
                }
            },

            right: {
                id: "n34",
                type: "number",
                value: 3
            }
        }
    }
};


/* ============================================================
 * Build AST ID -> node map
 * ============================================================
 */

function buildAstMap(
    root: AstNode
): Map<string, AstNode> {

    const nodes =
        new Map<string, AstNode>();


    function visit(
        node: AstNode
    ): void {

        nodes.set(
            node.id,
            node
        );


        switch (node.type) {

            case "number":
            case "variable":

                return;


            case "add":

                for (
                    const term of node.terms
                ) {
                    visit(term);
                }

                return;


            case "multiply":

                for (
                    const factor of node.factors
                ) {
                    visit(factor);
                }

                return;


            case "binary":

                visit(node.left);
                visit(node.right);

                return;


            case "root":

                if (node.degree) {
                    visit(
                        node.degree
                    );
                }

                visit(
                    node.radicand
                );

                return;


            case "integral":

                visit(
                    node.variable
                );

                visit(
                    node.lower
                );

                visit(
                    node.upper
                );

                visit(
                    node.integrand
                );

                return;


            case "limit":

                visit(
                    node.variable
                );

                visit(
                    node.target
                );

                visit(
                    node.expression
                );

                return;
        }
    }


    visit(root);

    return nodes;
}


const ast_nodes =
    buildAstMap(ast);


/* ============================================================
 * LaTeX generation
 * ============================================================
 */

const PRECEDENCE_ADD = 10;
const PRECEDENCE_MULTIPLY = 20;
const PRECEDENCE_POWER = 30;
const PRECEDENCE_ATOM = 100;


function getPrecedence(
    node: AstNode
): number {

    switch (node.type) {

        case "number":
        case "variable":
        case "root":
        case "integral":
        case "limit":

            return PRECEDENCE_ATOM;


        case "add":

            return PRECEDENCE_ADD;


        case "multiply":

            return PRECEDENCE_MULTIPLY;


        case "binary":

            switch (node.operator) {

                case "-":

                    return PRECEDENCE_ADD;


                case "/":

                    return PRECEDENCE_MULTIPLY;


                case "^":

                    return PRECEDENCE_POWER;
            }
    }
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

function associativeSeparator(parent_id: string, separator_index: number, latex: string): string {
    return htmlData(
        {
            assocsep: parent_id,
            sepindex: separator_index
        },
        latex
    );
}

function toLatex(node: AstNode,parent_precedence = 0,associative_position?: AssociativePosition): string {

    let body: string;

    switch (node.type) {
        case "number":
            body = String(node.value);

            break;


        case "variable":

            body = node.name;
            break;

        case "add": {

            const parts: string[] = [];

            for (let index = 0; index < node.terms.length; ++index) {
                if (index > 0) {

                    parts.push( associativeSeparator(node.id, index - 1, "+") );
                }

                parts.push(
                    toLatex(
                        node.terms[index],
                        PRECEDENCE_ADD,
                        {
                            parentId: node.id,
                            index
                        }
                    )
                );
            }

            body = parts.join(" ");

            break;
        }

        case "multiply": {

            const parts: string[] = [];

            for (let index = 0; index < node.factors.length; ++index) {
                if (index > 0) {

                    parts.push(
                        associativeSeparator(
                            node.id,
                            index - 1,
                            "\\cdot"
                        )
                    );
                }

                parts.push(
                    toLatex(
                        node.factors[index],
                        PRECEDENCE_MULTIPLY,
                        {
                            parentId: node.id,
                            index
                        }
                    )
                );
            }

            body =
                parts.join(" ");

            break;
        }

        case "binary": {
            switch (node.operator) {
                case "-":

                    body =
                        `${toLatex(
                            node.left,
                            PRECEDENCE_ADD
                        )} - ${toLatex(
                            node.right,
                            PRECEDENCE_ADD + 1
                        )}`;

                    break;


                case "/":

                    body =
                        `\\frac{` +
                        `${toLatex(node.left)}` +
                        `}{` +
                        `${toLatex(node.right)}` +
                        `}`;

                    break;


                case "^":

                    body =
                        `{${toLatex(
                            node.left,
                            PRECEDENCE_POWER
                        )}}` +
                        `^{${toLatex(
                            node.right
                        )}}`;

                    break;
            }

            break;
        }


        case "root": {

            const radicand =
                toLatex(node.radicand);

            if (node.degree) {

                body =
                    `\\sqrt[` +
                    `${toLatex(node.degree)}` +
                    `]{${radicand}}`;
            }
            else {

                body =
                    `\\sqrt{${radicand}}`;
            }

            break;
        }

        case "integral":
            body =
                `\\displaystyle ` +
                `\\int_{${toLatex(node.lower)}}` +
                `^{${toLatex(node.upper)}} ` +
                `${toLatex(node.integrand)}` +
                `\\,d${toLatex(node.variable)}`;

            break;

        case "limit":
            body =
                `\\displaystyle ` +
                `\\lim_{${toLatex(node.variable)}` +
                `\\to${toLatex(node.target)}} ` +
                `${toLatex(node.expression)}`;

            break;
    }


    if (getPrecedence(node) < parent_precedence) {
        body = `\\left(${body}\\right)`;
    }

    const attributes: Record<string, string | number> = {
        astid: node.id
    };


    if (associative_position) {
        attributes.assocparent = associative_position.parentId;

        attributes.associndex = associative_position.index;
    }

    return htmlData(attributes, body);
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
 * Result display
 * ============================================================
 */

function showResult( 
    result: HTMLElement, 
    ast_id: string | null
): void {

    if ( 
        ast_id === null
    ) {

        result.textContent = 
            "No AST node is completely contained.";

        return;
    }


    const node = 
        ast_nodes.get( 
            ast_id
        );


    if (!node) {

        result.textContent = 
            `Unknown AST node: ${ast_id}`;

        return;
    }


    result.textContent = 
        `Selected AST ID: ${ast_id}` + 
        `\n\n` +
        JSON.stringify( 
            node, 
            null, 
            2 
        );
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

const latex = toLatex( ast);

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


export function initTexTest(){}