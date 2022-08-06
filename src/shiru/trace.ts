type Stack = {
	name: string,
	start: number,
	end: null | number,
	children: Stack[],
	parent: Stack | null,
};

const root: Stack = {
	name: "root",
	start: performance.now(),
	end: null,
	children: [],
	parent: null,
};

let stack: Stack = root;

export function start(name: string): void {
	const e = {
		name,
		start: performance.now(),
		end: null,
		children: [],
		parent: stack,
	};
	stack.children.push(e);
	stack = e;
}

export function stop(name?: string): void {
	if (name !== undefined && name !== stack.name) {
		throw new Error("mismatched stack");
	}
	stack.end = performance.now();
	const parent = stack.parent;
	if (!parent) {
		throw new Error("mismatched stack");
	}
	stack = parent;
}

function escapeHtml(text: string): string {
	return text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

export function renderTree(stack: Stack, out: string[]): void {
	out.push("<details>");
	out.push("<summary>");
	const duration = stack.end ? (stack.end - stack.start).toFixed(1) : "?";
	out.push("<span class=numeral>" + duration + " ms</span> &mdash; ");
	out.push(escapeHtml(stack.name));
	out.push("</summary>");
	out.push("<ul>");
	for (const child of stack.children) {
		renderTree(child, out);
	}
	out.push("</ul>");
	out.push("</details>");
}

export function render(): string {
	const out: string[] = [`
<style>
body {
	font-family: sans-serif;
}

details {
	padding: 0.25em;
}

.numeral {
	display: inline-block;
	width: 7em;
	text-align: right;
}
</style>

`];
	renderTree(root, out);
	return out.join("\n");
}
