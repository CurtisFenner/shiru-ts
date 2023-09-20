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
	} | {
		tag: "playing",
		runForMs: number,
		playedAtMs: number,
	} = {
			tag: "paused",
			runForMs: 0,
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
	stopThreshold(0, title);
}

export function stopThreshold(thresholdMs: number, title?: string): void {
	if (title !== undefined && title !== activeStack.title) {
		throw new Error("mismatched stack:\n\t" + JSON.stringify(title) + "\n\t!=\n\t" + JSON.stringify(activeStack.title));
	}
	activeStack.end = stopwatch.measureMs();
	const parent = activeStack.parent;
	if (!parent) {
		throw new Error("mismatched stack:\n\tno stack open for\n\t" + JSON.stringify(title));
	}
	if (activeStack.end - activeStack.start < thresholdMs) {
		parent.children.pop();
	}
	activeStack = parent;
}

function showValue(x: unknown): [string, string] {
	const s = JSON.stringify(x, (key, value) => {
		if (typeof value === "bigint") {
			return value.toString() + "n";
		} else if (typeof value === "symbol") {
			return String(value);
		} else {
			return value;
		}
	});

	if (typeof x === "string") {
		return [x, ""];
	}

	return ["", String(s)];
}

function limitPrecision(n: number | null): number | null {
	if (n === null) {
		return null;
	}
	return parseFloat(n.toFixed(3));
}

function serialize(tree: Trace): unknown {
	if (tree.tag === "trace-branch") {
		return {
			title: typeof tree.title === "string"
				? [tree.title]
				: tree.title.flatMap(showValue),
			start: limitPrecision(tree.start),
			end: limitPrecision(tree.end),
			children: tree.children.map(serialize),
		};
	} else {
		return {
			title: typeof tree.title === "string"
				? [tree.title]
				: tree.title.flatMap(showValue),
			start: limitPrecision(tree.time),
			details: tree.details,
		};
	}
}

export function publish(): TraceBranch {
	root.end = stopwatch.measureMs();
	return root;
}

function encodeBase64(bytes: Uint8Array): string {
	return Buffer.from(bytes).toString("base64")
}

declare class CompressionStream {
	constructor(format: "gzip");
	readable: any;
	writable: any;
}

async function compressAndBase64Encode(bytes: Uint8Array): Promise<string> {
	const cs = new CompressionStream("gzip");
	const writer = cs.writable.getWriter();
	await writer.write(bytes);
	await writer.close();

	const reader = cs.readable.getReader();
	const chunks: BlobPart[] = [];
	while (true) {
		const { value, done } = await reader.read();

		if (value) {
			chunks.push(value);
		}
		if (done) {
			break;
		}
	}

	const buffer = await new Blob(chunks).arrayBuffer();
	return encodeBase64(new Uint8Array(buffer));
}

export async function render(branches: TraceBranch[]): Promise<string> {
	const data = JSON.stringify(branches.map(serialize));
	const toEmbed = await compressAndBase64Encode(new TextEncoder().encode(data));

	return `
<meta charset="utf-8">
<style>
body {
	font-family: sans-serif;
	line-height: 1.5rem;
}

summary {
	/* Align the expand arrow with li bullets */
	list-style-position: outside;
}

li, details {
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
<script type="text/plain" id="data">
${toEmbed}
</script>
<ul class="perf-box" id="perf-box">
</ul>
<script type="module">

async function decodeBase64Short(str) {
	const dataUrl = "data:application/octet-binary;base64," + str;
	const r = await fetch(dataUrl);
	return new Uint8Array(await r.arrayBuffer());
}

async function decodeBase64(str) {
	const stride = 100 * 3;
	const chunks = [];
	for (let i = 0; i < str.length; i += stride) {
		const encodedChunk = str.substring(i, Math.min(str.length, i + stride));
		chunks.push(await decodeBase64Short(encodedChunk));
	}

	return new Blob(chunks);
}

async function decodeBase64AndDecompress(str) {
	const compressed = await decodeBase64(str);
	const ds = new DecompressionStream("gzip");
	const decompressedStream = compressed.stream().pipeThrough(ds);
	const decompressed = await new Response(decompressedStream).blob();
	return await decompressed.text();
}

const data = document.getElementById("data").textContent.replace(/\\s+/g, "");
const roots = JSON.parse(await decodeBase64AndDecompress(data));

function formatNumber(n) {
	if (n < 10) {
		return n.toFixed(1);
	} else {
		return n.toFixed(0);
	}
}

function renderTitle(title) {
	const span = document.createElement("span");
	let parity = 0;
	for (let i = 0; i < title.length; i++) {
		const e = title[i];
		let node = document.createTextNode(" " + String(e) + " ");
		if (i % 2 === 1) {
			if (String(e).trim() === "") {
				continue;
			}
			const code = document.createElement("code");
			code.appendChild(node);
			node = code;
		}
		span.appendChild(node);
	}
	return span;
}

function renderTree(tree, into, context) {
	const details = (tree.children || ("details" in tree && tree.details))
		? document.createElement("details")
		: document.createElement("li");
	const summary = document.createElement("summary");
	let expand = document.createElement("ul");
	const sparkBox = document.createElement("div");
	sparkBox.className = "perf-spark";
	const sparkBar = document.createElement("div");
	sparkBar.className = "bar";
	const numeral = document.createElement("span");
	numeral.className = "numeral";

	const a0 = context.root.start;
	const a1 = (context.root.end || NaN);
	const t0 = tree.start;
	const t1 = tree.end || tree.start;
	const p0 = (t0 - a0) / (a1 - a0) * 100;
	const p1 = (t1 - a0) / (a1 - a0) * 100;
	sparkBar.style.left = p0.toFixed(3) + "%";
	sparkBar.style.right = (100 - p1).toFixed(3) + "%";

	const gap = document.createElement("span");
	gap.textContent = " — ";

	const elapsed = tree.end
		? formatNumber(tree.end - tree.start)
		: "?";
	if (!("details" in tree)) {
		numeral.textContent = elapsed + " ms";
	} else {
		gap.style.visibility = "hidden";
		if (tree.details) {
			expand = document.createElement("pre");
			const code = document.createElement("code");
			code.textContent = tree.details;
			expand.appendChild(code);
		}
	}

	const title = renderTitle(tree.title);

	sparkBox.appendChild(sparkBar);
	summary.appendChild(sparkBox);
	summary.appendChild(numeral);
	summary.appendChild(gap);
	summary.appendChild(title);
	details.appendChild(summary);
	details.appendChild(expand);
	into.appendChild(details);

	if (tree.children) {
		for (const child of tree.children) {
			renderTree(child, expand, context);
		}
		if (tree.children.length === 1) {
			details.open = true;
		}
	}
}

for (const root of roots) {
	console.log(root);
	renderTree(root, document.getElementById("perf-box"), {root});
}

</script>
`;
}
