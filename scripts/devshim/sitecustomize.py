"""Opt-in dev shim for running the harness inside the Claude-web container.

That container only allows outbound HTTPS through a TLS-re-terminating egress
proxy (CA at /root/.ccr/ca-bundle.crt). The harness's OpenRouter client pins
`trust_env=False`, which bypasses the proxy and gets policy-denied there.

This file activates ONLY when both are true:
  1. it is explicitly placed on PYTHONPATH  (PYTHONPATH=scripts/devshim run.py …)
  2. the container's proxy markers exist    (HTTPS_PROXY + the CA bundle file)

It then defaults httpx clients back to `trust_env=True` so they honor
HTTPS_PROXY and the standard CA env vars. TLS verification stays fully
enabled. The judging environment sets no PYTHONPATH and has no proxy markers,
so harness behavior there is exactly stock — this shim is dev tooling, not
part of the submission's runtime semantics.
"""

import os

if os.environ.get("HTTPS_PROXY") and os.path.exists("/root/.ccr/ca-bundle.crt"):
    try:
        import httpx

        _original_init = httpx.AsyncClient.__init__

        def _proxy_aware_init(self, *args, **kwargs):
            if kwargs.get("trust_env") is False:
                kwargs["trust_env"] = True
            return _original_init(self, *args, **kwargs)

        httpx.AsyncClient.__init__ = _proxy_aware_init
    except Exception:
        pass
