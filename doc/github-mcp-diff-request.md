# Feature request: patch/diff mode for create_or_update_file and push_files

Ready to file.  The MCP server in use here is `@modelcontextprotocol/server-github`
(the deprecated reference implementation); the official one is
`github/github-mcp-server`, which is where this should go.  It could not be
filed from this machine: the personal access token is scoped to thery's own
repositories, so it cannot open an issue in another organisation.

---

### Problem

`create_or_update_file` and `push_files` both require the **complete new
content** of every file touched.  That is unavoidable at the REST layer --
[Create a blob](https://docs.github.com/en/rest/git/blobs) takes only `content`
and `encoding`, and no endpoint applies a patch -- but it is not unavoidable
for the MCP server, which holds the token and can fetch the current blob
itself.

The cost falls on the model, which has to re-emit whole files token by token.
A concrete case: a change of about 200 lines across three source files meant
re-transmitting roughly 2100 lines, three times in one afternoon, because each
commit re-sends every file in full.  It is slow, expensive, and error-prone --
one of those re-transmissions introduced a one-character difference from the
intended content, caught only by fetching the branch back and diffing it.

### Proposal

Accept a patch instead of full content, and let the server expand it:

1. server GETs the current blob for `path` at `branch`;
2. server applies the supplied unified diff;
3. server uploads the result through the existing blob/tree/commit path.

Sketch:

    {
      "path": "src/foo.c",
      "patch": "@@ -12,3 +12,4 @@\n context\n-old line\n+new line\n context\n",
      "base_sha": "<blob sha the patch applies to>",
      "branch": "my-branch",
      "message": "..."
    }

`content` and `patch` mutually exclusive; `patch` absent keeps today's
behaviour exactly.  Failure to apply should be a clear error rather than a
partial write, and `base_sha` lets the server return a conflict instead of
silently patching a file that moved underneath.  The same field on `push_files`
entries covers the multi-file case, where the saving is largest.

### Why it is worth it

Every agent committing repeatedly to the same files pays this on each commit,
and the cost grows with file size rather than with the size of the change.
Diffs are also what a model already produces when editing, so the conversion is
natural and the payload shrinks by one to two orders of magnitude.

This is more work than a thin API wrapper, since it puts patch application
inside the server.  It seems worth it: the alternative for anyone hitting this
is to leave MCP and shell out to `git push`, which sends deltas over git's own
protocol and takes a second.
