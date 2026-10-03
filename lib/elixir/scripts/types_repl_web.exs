# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: 2021 The Elixir Team

unless Code.ensure_loaded?(Module.Types.Repl) do
  Code.require_file("../lib/module/types/repl.ex", __DIR__)
end

unless Code.ensure_loaded?(Module.Types.Repl.Web.CLI) do
  Code.require_file("../lib/module/types/repl_web.ex", __DIR__)
end

Module.Types.Repl.Web.CLI.main(System.argv())
