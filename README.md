# Nova Version 4

Complete v4.0.0 build of the Nova Proxy panel: readable source, obfuscated build, and the frontend.

## What's in here

| File / folder | What it is |
|---|---|
| `sourcecode.optimized.bundled.js` | **The actual, readable worker source** (V4.0.0). This is the code you edit. |
| `worker.js` | The **obfuscated build** produced from the source above. This is what gets deployed to Cloudflare. Not meant to be read or edited by hand. |
| `public/` | The **frontend panel** (admin / login / user / install pages, `nova-admin.js`, logos, version.json). Served from the worker's own domain via the Cloudflare `ASSETS` binding. |
| `wrangler.jsonc` | Cloudflare config: binds the panel (`ASSETS`), the D1 database (`DB`), and the vars. |
| `schema.sql` | The D1 table schema (the worker also creates its own tables on first run). |
| `build-worker.sh` | Builds `worker.js` from the source (esbuild + obfuscation, keeps the `cloudflare:sockets` specifier external). |
| `package.json` | Dependencies for building. |

## Edit -> build -> run

1. Edit `sourcecode.optimized.bundled.js` (the source) and/or files in `public/` (the panel UI).
2. Rebuild the deployable worker:
   ```
   ./build-worker.sh sourcecode.optimized.bundled.js worker.js
   ```
3. Run locally to preview the whole panel:
   ```
   npx wrangler@4 dev --port 8787 --local --local-protocol https
   ```
   Then open **https://localhost:8787/login** (accept the local self-signed cert).
   First run: open `/install` to set an admin password, then log in.

Notes:
- It must be **https** locally, the worker force-redirects http to https.
- Local mode uses a simulated D1 (nothing touches Cloudflare). Proxying itself only works on the real edge; the panel UX is fully browsable locally.
- Run only **one** `wrangler dev` at a time, multiple instances deadlock the local D1 (`SQLITE_BUSY`).
