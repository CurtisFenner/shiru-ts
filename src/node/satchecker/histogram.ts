const SOLID_BLOCK = "#";
const EMPTY_BLOCK = "_";

export class Histogram {
	private buckets: number[] = [];
	private sum: number = 0;
	private count: number = 0;

	constructor(private bucketSize: number, bucketCount: number) {
		for (let i = 0; i < bucketCount; i++) {
			this.buckets.push(0);
		}
	}

	record(n: number): void {
		this.sum += n;
		this.count += 1;
		const index = Math.min(Math.floor(Math.max(0, n / this.bucketSize)), this.buckets.length - 1);
		this.buckets[index] += 1;
	}

	print(title: string, labeler: (lo: number, hi: number, last: boolean) => string): string[] {
		const lines = [];
		lines.push(title);
		lines.push("\t  Count:\t" + this.count);
		lines.push("\tAverage:\t" + (this.sum / this.count).toFixed(1));
		const labels = [];
		for (let i = 0; i < this.buckets.length; i++) {
			let label = labeler(i * this.bucketSize, (i + 1) * this.bucketSize, i == this.buckets.length - 1);
			labels.push(label);
		}
		const longestLabel = Math.max(...labels.map(x => x.length));

		const DIAGRAM_WIDTH = 40;
		const widest = Math.max(...this.buckets);
		const scaling = Math.min(1, DIAGRAM_WIDTH / widest);

		for (let i = 0; i < this.buckets.length; i++) {
			const labelPadding = " ".repeat(longestLabel - labels[i].length);
			let w = this.buckets[i] * scaling;
			if (w > 0) {
				w = Math.max(w, 1);
			}
			w = Math.floor(w);
			const bars = SOLID_BLOCK.repeat(w) + EMPTY_BLOCK.repeat(DIAGRAM_WIDTH - w);
			lines.push("\t" + labelPadding + labels[i] + ": " + bars + " " + this.buckets[i]);
		}
		return lines;
	}
}
