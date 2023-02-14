import * as child_process from "child_process";
import * as os from "os";
import * as fs from "fs";
import * as path from "path";

const TMP = os.tmpdir();

// Read SHAs from command line arguments.
const commandArguments = process.argv.slice(2);

const shas = commandArguments;
for (const sha of shas) {
	if (!sha.match(/^[\.0-9a-zA-Z_\/-]+$/)) {
		throw new Error("invalid sha `" + sha + "`");
	}
}

// Propose directory names and resolve each SHA.
const nowString = new Date().toISOString().replace(/[^0-9]+/g, "");
const workingDirectories = [];
for (let i = 0; i < shas.length; i++) {
	const sha = shas[i];
	const wd = path.join(TMP, "shiru-comparison-" + nowString + "-" + i + "-" + sha);
	workingDirectories.push({ wd, sha });

	try {
		console.error(child_process.execSync("git log -1 --stat " + sha).toString("utf8"));
	} catch {
		throw new Error("git could not find sha `" + sha + "`");
	}
	console.log(wd);
	console.log("");
}

try {
	// Create repositories in a temporary directory.
	const data: Record<string, any[]> = {};
	const times: Record<string, string> = {};
	for (const { wd, sha } of workingDirectories) {
		child_process.execSync("git clone . " + wd);
		child_process.execSync("git checkout " + sha, {
			cwd: wd,
		});
		child_process.execSync("yarn build", {
			cwd: wd,
		});
		child_process.execSync("yarn test", {
			cwd: wd,
		});
		const epochTimeString = child_process.execSync("git show -s --format=%ct", {
			cwd: wd,
			encoding: "utf-8",
		});
		const epochTime = new Date(1000 * parseInt(epochTimeString, 10));
		times[sha] = epochTime.toString();
		data[sha] = [];
	}

	const STRIPES = 3;
	const STRIPE_RUNS = 3;
	const total = STRIPES * STRIPE_RUNS * workingDirectories.length;
	const startTime = Date.now();
	let progress = 0;
	let lastEstimateTotalSeconds = 0;
	for (let i = 0; i < STRIPES; i++) {
		for (const { wd, sha } of workingDirectories) {
			for (let j = 0; j < STRIPE_RUNS; j++) {
				const perfFile = "perf-" + i + "-" + j + ".json";
				child_process.execSync("yarn test perf=" + perfFile, {
					cwd: wd,
				});
				const content = fs.readFileSync(path.join(wd, perfFile), { encoding: "utf-8" });
				data[sha].push({ ...JSON.parse(content), timestamp: times[sha] });

				progress += 1;
				const elapsedMillis = Date.now() - startTime;
				const completed = progress / total;
				const millisPerRun = elapsedMillis / progress;
				const estimateRemainingMillis = (total - progress) * millisPerRun;
				const estimateRemainingSeconds = estimateRemainingMillis / 1000;
				const estimateTotalSeconds = elapsedMillis / 1000 + estimateRemainingSeconds;
				const change = estimateTotalSeconds - lastEstimateTotalSeconds;
				const percentage = (100 * completed).toFixed(0).padStart(3, " ") + "%";
				let delta = change.toFixed(1);
				if (delta[0] !== "-" && change > 0) {
					delta = "+" + delta;
				}
				lastEstimateTotalSeconds = estimateTotalSeconds;
				console.log(percentage + ", about "
					+ estimateRemainingSeconds.toFixed(1).padStart(5, " ")
					+ " seconds remaining (total " + estimateTotalSeconds.toFixed(1) + " seconds, " + delta + " seconds)");
			}
		}
	}

	// Write out all the collected data.
	const outFile = "combined-perf.json";
	fs.writeFileSync(outFile, JSON.stringify(data));
	console.error("wrote to `" + outFile + "`");
} catch (e) {
	console.error(e);
} finally {
	// Clean up the temporary directories.
	for (const { wd } of workingDirectories) {
		try {
			fs.rmSync(wd, { recursive: true });
			console.error("deleted", wd);
		} catch (e) {
			console.error(e);
			console.error("could not clean up temporary working directory\n\t" + wd);
		}
	}
}
