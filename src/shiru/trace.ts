type Trace = TraceBranch | TraceDetails;

type TraceDetails = {
	tag: "trace-details",
	title: string,
	details: string,
	time: number,
	parent: Trace | null,
};

type TraceBranch = {
	tag: "trace-branch",
	title: string,
	start: number,
	end: null | number,
	children: Trace[],
	parent: TraceBranch | null,
};

const root: TraceBranch = {
	tag: "trace-branch",
	title: "root",
	start: performance.now(),
	end: null,
	children: [],
	parent: null,
};

let activeStack: TraceBranch = root;

let slow = false;

export function setSlow(newSlow: boolean) {
	slow = newSlow;
}

export function start(title: unknown): void {
	const e: TraceBranch = {
		tag: "trace-branch",
		title: typeof title === "string" ? title : JSON.stringify(title),
		start: performance.now(),
		end: null,
		children: [],
		parent: activeStack,
	};
	activeStack.children.push(e);
	activeStack = e;
}

export function mark(title: string, details: () => string): void {
	const e: TraceDetails = {
		tag: "trace-details",
		title,
		details: slow ? details() : "(details skipped because trace.slow is false)",
		time: performance.now(),
		parent: activeStack,
	};
	activeStack.children.push(e);
}

export function stop(title?: string): void {
	if (title !== undefined && title !== activeStack.title) {
		throw new Error("mismatched stack:\n\t" + JSON.stringify(title) + "\n\t!=\n\t" + JSON.stringify(activeStack.title));
	}
	activeStack.end = performance.now();
	const parent = activeStack.parent;
	if (!parent) {
		throw new Error("mismatched stack:\n\tno stack open for\n\t" + JSON.stringify(title));
	}
	activeStack = parent;
}

function escapeHtml(text: unknown): string {
	if (typeof text !== "string") {
		return "<code>" + escapeHtml(JSON.stringify(text)) + "</code>";
	}
	return text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

function renderTrees(stacks: Trace[], out: string[], settings: { root: TraceBranch }) {
	for (const child of stacks) {
		renderTree(child, out, { open: stacks.length < 2, root: settings.root });
	}
}

function getDurationMs(stack: TraceBranch): number {
	if (stack.end === null) {
		return 0;
	}
	return stack.end - stack.start;
}

export function renderTree(stack: Trace, out: string[], settings: { open: boolean, root: TraceBranch }): void {
	if (stack.tag === "trace-branch") {
		out.push("<details " + (settings.open ? "open" : "") + ">");
		out.push("<summary>");
		out.push("<div class=perf-spark>");
		const totalPercentage = 100 * getDurationMs(stack) / getDurationMs(settings.root);
		out.push(`<div class=bar style="width: ${totalPercentage.toFixed(2)}%"></div>`);
		out.push("</div>");
		const durationText = stack.end ? getDurationMs(stack).toFixed(1) : "?";
		out.push("<span class=numeral>" + durationText + " ms</span> &mdash; ");
		out.push(escapeHtml(stack.title));
		out.push("</summary>");
		out.push("<ul>");
		renderTrees(stack.children, out, { root: settings.root });
		out.push("</ul>");
		out.push("</details>");
	} else {
		out.push("<details>");
		out.push("<summary>");
		out.push(escapeHtml(stack.title));
		out.push("</summary>");
		out.push("<pre><code>" + escapeHtml(stack.details) + "</code></pre>");
		out.push("</details>");
	}
}

export function render(): string {
	root.end = performance.now();
	const out: string[] = [`
<style>
body {
	font-family: sans-serif;
}

details {
	padding: 0.25em;
}

pre {
	background: #FED;
	padding: 1em;
	border: 1px dotted #BBB;
	color: #012;
}

.numeral {
	display: inline-block;
	width: 7em;
	text-align: right;
	font-weight: bold;
}

.perf-box {
	position: relative;
	padding-left: 8em;
}

.perf-spark {
	display: inline-block;
	position: absolute;
	left: 0.5em;
	height: 1em;
	width: 7em;
	border: 1px solid black;
	background: white;
}
.perf-spark .bar {
	display: block;
	position: absolute;
	background: black;
	top: 0;
	left: 0;
	bottom: 0;
}
</style>

<body>
<div class=perf-box>

`];
	renderTrees([root], out, { root });
	out.push(`
</div>
	`);
	return out.join("\n");
}
