export type Trace = TraceBranch | TraceDetails;

type TraceDetails = {
	tag: "trace-details",
	title: string | unknown[],
	details: string | null,
	time: number,
	parent: Trace | null,
};

export type TraceBranch = {
	tag: "trace-branch",
	title: string | unknown[],
	start: number,
	end: null | number,
	children: Trace[],
	parent: TraceBranch | null,
};

export class Stopwatch {
	constructor(private internalClock: () => number) { }

	state: {
		tag: "paused",
		runForMs: number,
		pausedAtMs: number,
	} | {
		tag: "playing",
		runForMs: number,
		playedAtMs: number,
	} = {
			tag: "paused",
			runForMs: 0,
			pausedAtMs: this.internalClock(),
		};


	resume() {
		if (this.state.tag === "playing") {
			return;
		}
		this.state = {
			tag: "playing",
			runForMs: this.state.runForMs,
			playedAtMs: this.internalClock(),
		};
	}

	pause() {
		if (this.state.tag === "paused") {
			return;
		}
		const now = this.internalClock();
		this.state = {
			tag: "paused",
			runForMs: this.state.runForMs + now - this.state.playedAtMs,
			pausedAtMs: now,
		};
	}

	measureMs(): number {
		if (this.state.tag === "paused") {
			return this.state.runForMs;
		} else {
			const now = this.internalClock();
			return this.state.runForMs + now - this.state.playedAtMs;
		}
	}
}

const stopwatch = new Stopwatch(() => performance.now());

export function clear(title: string) {
	root = {
		tag: "trace-branch",
		title,
		start: stopwatch.measureMs(),
		end: null,
		children: [],
		parent: null,
	};

	activeStack = root;
}

let root: TraceBranch = {
	tag: "trace-branch",
	title: "root",
	start: stopwatch.measureMs(),
	end: null,
	children: [],
	parent: null,
};

let activeStack: TraceBranch = root;

let slow = false;

export function setSlow(newSlow: boolean) {
	slow = newSlow;
}

export function start(title: string | unknown[]): void {
	const e: TraceBranch = {
		tag: "trace-branch",
		title,
		start: stopwatch.measureMs(),
		end: null,
		children: [],
		parent: activeStack,
	};
	activeStack.children.push(e);
	activeStack = e;
}

export function mark(title: string | unknown[], details?: () => string): void {
	stopwatch.pause();
	const e: TraceDetails = {
		tag: "trace-details",
		title,
		details: details
			? (slow ? details() : "(details skipped because trace.slow is false)")
			: null,
		time: stopwatch.measureMs(),
		parent: activeStack,
	};
	activeStack.children.push(e);
	stopwatch.resume();
}

export function stop(title?: string): void {
	if (title !== undefined && title !== activeStack.title) {
		throw new Error("mismatched stack:\n\t" + JSON.stringify(title) + "\n\t!=\n\t" + JSON.stringify(activeStack.title));
	}
	activeStack.end = stopwatch.measureMs();
	const parent = activeStack.parent;
	if (!parent) {
		throw new Error("mismatched stack:\n\tno stack open for\n\t" + JSON.stringify(title));
	}
	activeStack = parent;
}

function showValue(x: unknown): string {
	const s = JSON.stringify(x, (key, value) => {
		if (typeof value === "bigint") {
			return value.toString() + "n";
		} else {
			return value;
		}
	});

	return String(s);
}

function escapeHtml(text: unknown): string {
	if (typeof text !== "string") {
		return "<code>" + escapeHtml(showValue(text)) + "</code>";
	}
	return text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

function renderTrees(stacks: Trace[], out: string[], settings: { totalTimeMs: number }) {
	for (const child of stacks) {
		renderTree(child, out, { open: stacks.length < 2, totalTimeMs: settings.totalTimeMs });
	}
}

function getDurationMs(stack: TraceBranch): number {
	if (stack.end === null) {
		return 0;
	}
	return stack.end - stack.start;
}

export function renderTree(stack: Trace, out: string[], settings: { open: boolean, totalTimeMs: number }): void {
	if (stack.tag === "trace-branch") {
		out.push("<details " + (settings.open ? "open" : "") + ">");
		out.push("<summary>");
		out.push("<div class=perf-spark>");
		const totalPercentage = 100 * getDurationMs(stack) / settings.totalTimeMs;
		const startPercentage = 100 * stack.start / settings.totalTimeMs;
		out.push(`<div class=bar style="left: ${startPercentage.toFixed(2)}%; width: ${totalPercentage.toFixed(2)}%"></div>`);
		out.push("</div>");
		const durationText = stack.end ? getDurationMs(stack).toFixed(1) : "?";
		out.push("<span class=numeral>" + durationText + " ms</span> &mdash; ");
		const title: unknown[] = Array.isArray(stack.title) ? stack.title : [stack.title];
		for (const element of title) {
			out.push(escapeHtml(element));
		}
		out.push("</summary>");
		out.push("<ul>");
		renderTrees(stack.children, out, { totalTimeMs: settings.totalTimeMs });
		out.push("</ul>");
		out.push("</details>");
	} else {
		if (stack.details === null) {
			out.push("<li>");
			const title: unknown[] = Array.isArray(stack.title) ? stack.title : [stack.title];
			for (const element of title) {
				out.push(escapeHtml(element));
			}
			out.push("</li>");
		} else {
			out.push("<details>");
			out.push("<summary>");
			const title: unknown[] = Array.isArray(stack.title) ? stack.title : [stack.title];
			for (const element of title) {
				out.push(escapeHtml(element));
			}
			out.push("</summary>");
			out.push("<pre><code>" + escapeHtml(stack.details) + "</code></pre>");
			out.push("</details>");
		}
	}
}

export function publish(): TraceBranch {
	root.end = stopwatch.measureMs();
	return root;
}

export function render(branches: TraceBranch[]): string {
	const out: string[] = [`
<style>
body {
	font-family: sans-serif;
	line-height: 1.5rem;
}

summary {
	/* Align the expand arrow with li bullets */
	list-style-position: outside;
}

details {
	padding: 0.25em;
}

code {
	background: #FFFAF5;
	display: inline-block;
	border: 1px dotted #BBB;
	color: #00050A;
	padding: 0.25em;
	margin-top: -0.125em;
	margin-bottom: -0.125em;
}

pre code {
	padding: 1em;
	display: block;
}

.numeral {
	display: inline-block;
	width: 5.5em;
	text-align: right;
	font-weight: bold;
}

.perf-box {
	position: relative;
	padding-left: 9em;
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
	for (const branch of branches) {
		renderTree(branch, out, {
			open: true,
			totalTimeMs: getDurationMs(branch),
		});
	}
	out.push(`
</div>
	`);
	return out.join("\n");
}
