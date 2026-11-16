# GitHub Forge Clone

A standalone, GitHub-compatible git forge in a single Python file (`main.py`,
standard library only). One process serves four surfaces from its own
in-memory store:

- **Git smart HTTP** — upload-pack protocol v2 (`ls-refs`, `fetch`) and
  receive-pack v0 (push), with exact closure-difference packs and shallow
  support.
- **REST v3 API** under `/api/v3` — repositories, contents, git refs,
  branches, commits, labels, issues, comments and pull requests with a real
  squash-merge engine.
- **GraphQL v4 API** at `/api/graphql` — queries, mutations, connections and
  introspection over the same store.
- **MCP endpoint** at `/mcp` — JSON-RPC 2.0 tools over the same store.

The forge registers its ephemeral port with the trial environment
(`MAKEFUN_ENV_URL`), serves until the environment says the trial is done, and
exits 0. All state lives in memory; nothing is persisted.

Run it the way the trial does:

```
python3 -P -s main.py
```

(with `MAKEFUN_ENV_URL` and `MAKEFUN_SHOP_TOKEN` set in the environment).

## License

MIT — see `LICENSE`.
