#!/usr/bin/python
#
# This file is part of pampel.
#
# pampel is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# pampel is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with pampel.  If not, see <http://www.gnu.org/licenses/>.
#


import pygit2 as git

import argparse
import fnmatch
import shutil
import os
import sys
import re
import subprocess
import datetime
import json
import imp
import functools
import numbers
import six
from contextlib import contextmanager
from threading import Thread


PROG = os.path.basename(sys.argv[0])

out_dir_re = re.compile("out($|-?)") # output dirs are either "out" or "out-*"
author = git.Signature(PROG, PROG)
committer = author

pampel_commit_re = re.compile(r'pampel [[]run #([0-9]+)[]]$', re.M)


# see http://stackoverflow.com/questions/14986490/python-change-sys-stdout-print-to-custom-print-function
class _RedirectPrint():
    def __init__(self, stdout):
        self.old_stdout = stdout
        self.nl = True

    def write(self, text):
        for l in text.splitlines(True):
            if self.nl:
                self.old_stdout.write('> ' + l)
            else:
                self.old_stdout.write(l)
            self.nl = l.endswith("\n")

@contextmanager
def _redirect_12():
    old_stdout = sys.stdout
    old_stderr = sys.stderr

    sys.stdout = _RedirectPrint(old_stdout)
    sys.stdout = _RedirectPrint(old_stderr)

    try:
        yield
    finally:
        sys.stdout = old_stdout
        sys.stderr = old_stderr


class LL:
    FATAL   = 0
    ERROR   = 1
    WARN    = 2
    INFO    = 3
    VERBOSE = 4
    DEBUG   = 5
    TRACE   = 6

def _color(name):
    if   name == "black":   c = "30"
    elif name == "red":     c = "31"
    elif name == "green":   c = "32"
    elif name == "yellow":  c = "33"
    elif name == "blue":    c = "34"
    elif name == "magenta": c = "35"
    elif name == "cyan":    c = "36"
    elif name == "white":   c = "37"
    elif name == "none":    c = "0"
    return '\033[' + c + 'm'


_LOGCOLORS = [ _color("red"), _color("red"), _color("red"), '', '', '', '' ]


if "_LOGLEVEL" not in globals():
    _LOGLEVEL = LL.INFO

if "_COLORED_OUTPUT" not in globals():
    _COLORED_OUTPUT = "auto"

if "_OUT_TTY" not in globals():
    _OUT_TTY = sys.stderr.isatty()


def is_colored():
    return _COLORED_OUTPUT == "always" \
            or (_COLORED_OUTPUT == "auto" and _OUT_TTY)


def _general_log(minlevel, prefix, *args):
    indent = len(prefix)
    msg = " ".join(map(str, args))
    cont_prefix = " " * (indent-1) + "> "
    
    c = _LOGCOLORS[minlevel] if is_colored() else ''
    prefix = c + prefix + " "

    if _LOGLEVEL >= minlevel:
        first_line = True
        for line in msg.splitlines(True):
            if first_line:
                sys.stderr.write(prefix + line)
                first_line = False
            else:
                sys.stderr.write(cont_prefix + line)
        if c:
            sys.stderr.write(_color("none"))
        sys.stderr.write("\n")

def fatallog(*args):
    _general_log(LL.FATAL, "[FTL]", *args)

def errorlog(*args):
    _general_log(LL.ERROR, "[ERR]", *args)

def warnlog(*args):
    _general_log(LL.WARN,  "[WRN]", *args)

def infolog(*args):
    _general_log(LL.INFO,  "[INF]", *args)

def verblog(*args):
    _general_log(LL.VERBOSE, "[DBG]", *args)

def debuglog(*args):
    _general_log(LL.DEBUG, "[DBG]", *args)

def tracelog(*args):
    _general_log(LL.TRACE, "[TRC]", *args)

def colorlog(clr, *args):
    c = _color(clr) if is_colored() else ''
    sys.stderr.write(
            c + " ".join(map(str, args))
            + (_color("none") if c else "")
            + "\n"
            )


class JsonFormattedEncoder:
    def __init__(self, indent=0):
        self.indent = indent
        self.encoder = json.JSONEncoder(sort_keys=True, indent=2, default=self.__class__.default)
        self.reset()

    def reset(self):
        self.in_obj = False
        self.json_str = ""
    
    def start_obj(self):
        assert not self.in_obj
        self.in_obj = True
        self.first_prop = True
        self.blank = False
        self.json_str += "  " * self.indent +  "{\n"
        self.indent += 1

    def end_obj(self):
        assert self.in_obj
        self.in_obj = False
        self.indent -= 1
        self.json_str += "\n" + "  " * self.indent + "}\n"

    def add_sep(self):
        if self.first_prop:
            self.first_prop = False
        else:
            self.json_str += ",\n"
        if self.blank: self.json_str += "\n"

    def blank_line(self):
        self.blank = True

    def add_props_table(self, kvs):
        assert self.in_obj
        self.add_sep()

        # get longest key
        maxlen = 0
        for kv in kvs:
            if kv is not None: maxlen = max(maxlen, len(kv[0]))
        maxlen += 4 # acount for quotation marks and colon
        key_fmt = "{{:{0}}}".format(maxlen)

        need_sep = False
        for kv in kvs:
            if need_sep:
                self.json_str += ",\n"
                need_sep = False

            if kv is None:
                self.json_str += "\n"
                continue
            k, v = kv
            self.json_str += "  " * self.indent + key_fmt.format("\"" + k + "\": ")
            val_str = self.encoder.encode(v)
            first_line = True
            for l in val_str.splitlines(True):
                if first_line:
                    self.json_str += l
                    first_line = False
                else:
                    self.json_str += "  " * self.indent + l
            need_sep = True
        self.first_prop = False

    def add_prop(self, k, v):
        self.add_props_table([(k, v)])

    def add_encoded_prop(self, k, val_str):
        assert isinstance(val_str, str)
        assert self.in_obj

        self.add_sep()

        self.json_str += " " * self.indent + "\"{0}\": ".format(k)
        first_line = True
        for l in val_str.splitlines():
            if first_line:
                self.json_str += l
                first_line = False
            else:
                self.json_str += "\n" + "  " * self.indent + l

    def encode(self, *args):
        return self.encoder.encode(*args)

    def __str__(self):
        assert not self.in_obj
        assert json.loads(self.json_str) is not None
        return self.json_str

    @staticmethod
    def default(o):
        if   isinstance(o, datetime.datetime):  return str(o)
        elif isinstance(o, datetime.timedelta): return str(o)
        elif isinstance(o, git.Oid):            return str(o)
        else: raise TypeError("Don't know how to generate a serializable object out of type {0}".format(type(o)))


def commit_to_json(commit):
    first, rest = commit.message.split("\n", 1)
    # debuglog("{} -- {}".format(first, commit.id))
    return json.loads(rest)


class PampelConfig:
    def __init__(self, repo):
        self.aux_repos = []
        self.run_count = 0
        self.snapshots = []
        self.command   = []
        self.import_script = False

        self.repo = repo

    def __enter__(self):
        self.load()
        return self

    def __exit__(self, typ, val, traceback):
        self.save()

    def set_attrs(self, kv):
        for k, t in [
                ("run_count", int),
                ("aux_repos", list),
                ("snapshots", list),
                ("command",   list),
                ("import_script", bool)
                ]:
            if k in kv:
                if isinstance(kv[k], t):
                    setattr(self, k, kv[k])
                else:
                    raise ValueError("attribute {0} has type {1} but {2} is expected".format(k, type(kv[k]), t))
    
    def load(self):
        p = os.path.join(self.repo.workdir, ".pampel.json")
        try:
            self.set_attrs(json.load(open(p, "r")))
        except FileNotFoundError:
            pass

    def save(self):
        d = {}
        for k, v in self.__dict__.items():
            if k != "repo": d[k] = v
        p = os.path.join(self.repo.workdir, ".pampel.json")
        debuglog("saving {0}".format(p))
        json.dump(d, open(p, "w"), indent=2, sort_keys=True)

    def stage(self):
        p = os.path.join(self.repo.workdir, ".pampel.json")
        debuglog("staging {0}".format(p))
        idx = self.repo.index
        # TODO less read/write
        idx.read()
        idx.add(".pampel.json")
        idx.write()

    def add_snapshot(self, path):
        try:
            repo = git.discover_repository(path)
        except KeyError:
            pass
        else:
            raise KeyError("path `{0}' already belongs to a git repository: {1}".format(path, repo))

        # TODO warning message: shared repo
        stat = subprocess.call(["git", "clone", "--shared", self.repo.workdir, path])
        assert stat == 0
        self.snapshots.append(os.path.realpath(path))

    def remove_snapshot(self, path):
        # TODO check that snapshot id clean
        try:
            snapshot = git.Repository(path)
        except Exception as e:
            errorlog("could not open repository at {} ({}):\n{}".format(path, type(e).__name__, e))
            raise e

        # check that snapshot really is shared with repo
        for l in open(os.path.join(snapshot.path, "objects", "info", "alternates"), "r"):
            l = l.rstrip("\n\r")
            if not l: break
            p1 = os.path.realpath(os.path.join(self.repo.path, "objects"))
            p2 = os.path.realpath(l)
            debuglog("p1 {}".format(p1))
            debuglog("p2 {}".format(p2))
            assert os.path.realpath(os.path.join(self.repo.path, "objects")) == os.path.realpath(l)

        # TODO: ask user for confirmation
        shutil.rmtree(path)
        self.snapshots.remove(os.path.realpath(path))


    def create_snapshot(self, path, commit, branch_name):
        if os.path.lexists(path):
            errorlog("snapshot path already exists: {}".format(path))
            assert False

        os.makedirs(path)

        self.add_snapshot(path)
        new_repo = git.Repository(path)

        # TODO switch to revparse in similar cases
        ncom = new_repo.revparse_single(str(commit.id))
        br = new_repo.create_branch(branch_name, ncom)
        new_repo.checkout(br)


def get_snapshot_dir(props, run_info, param_map=None, value_map=None):
    get_param = lambda k:    param_map[k]    if param_map is not None else k
    get_value = lambda k, v: value_map[k][v] if value_map is not None else v

    run_str = "{:03}".format(run_info["run count"])
    par_str = " ".join([
                "{}={}".format(get_param(k), get_value(k, v))
                for k, v in sorted(props.items())
                ])

    dirname = run_str
    if par_str: 
        dirname += " " + par_str
    else:
        dirname = "pampel-run-{}".format(run_str)

    return dirname


def is_repo_clean(repo):
    for f, s in repo.status().items():
        if s != git.GIT_STATUS_IGNORED:
            d = f.split(os.sep)[0]
            if s != git.GIT_STATUS_WT_DELETED or not out_dir_re.match(d):
                debuglog("path `{0}' is not clean".format(f))
                return False
    return True


def git_status_to_str(s):
    if   s == git.GIT_STATUS_CURRENT:
        return "current"
    elif s == git.GIT_STATUS_IGNORED:
        return "ignored"
    elif s == git.GIT_STATUS_INDEX_MODIFIED:
        return "index modified"
    elif s == git.GIT_STATUS_INDEX_DELETED:
        return "index deleted"
    elif s == git.GIT_STATUS_INDEX_NEW:
        return "index new"
    elif s == git.GIT_STATUS_WT_MODIFIED:
        return "wt modified"
    elif s == git.GIT_STATUS_WT_DELETED:
        return "wt deleted"
    elif s == git.GIT_STATUS_WT_NEW:
        return "wt new"
    
    raise ValueError("unkown git status: {0}".format(s))


# this function ignores deleted files in output directories
def is_repo_clean_output(repo):
    for f, s in repo.status().items():
        if s != git.GIT_STATUS_IGNORED:
            d = f.split(os.sep)[0]
            if s != git.GIT_STATUS_WT_DELETED and out_dir_re.match(d):
                debuglog("path `{0}' is not clean ({1})".format(f, git_status_to_str(s)))
                return False
    return True


def check_command_output(repo):
    """
    Check that the external command has only written to output directories
    """
    for f, s in repo.status().items():
        if s != git.GIT_STATUS_IGNORED:
            d = f.split(os.sep)[0]
            if f != ".pampel.json" and not out_dir_re.match(d):
                debuglog("path `{0}' is not clean ({1})".format(f, git_status_to_str(s)))
                return False
    return True


def git_stage(repo):
    idx = repo.index
    idx.read()
    
    for f, s in repo.status().items():
        if s == git.GIT_STATUS_IGNORED: continue

        if f == ".pampel-commit":
            debuglog("removing {}".format(f))
            os.remove(f)
            continue

        debuglog("staging path `{0}'".format(f, s))
        if s == git.GIT_STATUS_WT_DELETED:
            idx.remove(f)
        else:
            idx.add(f)
    idx.write()


def git_stage_output_dirs(repo):
    idx = repo.index
    idx.read()
    
    for f, s in repo.status().items():
        if s == git.GIT_STATUS_IGNORED: continue

        tracelog("pre stg path {0}, {1}".format(s, f))
        d = f.split("/")[0]
        if out_dir_re.match(d) and not os.path.isdir(f):
            debuglog("staging path {0}".format(f, s))
            if s == git.GIT_STATUS_WT_DELETED:
                idx.remove(f)
            else:
                idx.add(f)
    idx.write()


def clear_output_dirs(repo):
    infolog("clearing output directories")
    for d in os.listdir(repo.workdir):
        if not out_dir_re.match(d): continue
        p = os.path.join(repo.workdir, d)
        debuglog("clr {0}".format(p))
        if os.path.isdir(p):
            for sd in os.listdir(p):
                sp = os.path.join(p, sd)
                if os.path.isdir(sp):
                    shutil.rmtree(sp)
                else:
                    os.remove(sp)


# TODO: introduce "hidden" parameters which are not considered for snapshot
# names
# get short but unique string representation for each parameter name
def format_params(params):
    min_key_len = 3

    tree = [0, {}]

    # build tree
    for k in params:
        assert isinstance(k, str)
        level = tree
        for c in k:
            if c not in level[1]:
                level[1][c] = [1, {}]
            else:
                level[1][c][0] += 1
            level = level[1][c]

    param_map = {}
    for k in params:
        level = tree
        n = 0
        for c in k:
            n += 1
            level = level[1][c]
            if not level[1]:
                break
            if level[0] == 1 and n >= min_key_len:
                break
        param_map[k] = k[0:n]
    debuglog("param_map", param_map)

    return param_map


# get short but unique string representation for each parameter value
def format_values(params, pvs):
    min_prec = 4

    value_map = {} # { param: { value: value_str, ... }, ... }

    for p in params:
        v2s = {}     # maps a value to its string representation
        strs = set() # all string representations for the current parameter's values

        loop_count = 0
        max_loop = 1
        val_type = None

        while True:
            v2s.clear()
            strs.clear()

            for pv in pvs:
                if p in pv:
                    v = pv[p]
                    if v in v2s: continue

                    if isinstance(v, numbers.Number):
                        if loop_count == 0:
                            val_type = numbers.Number
                            max_loop = 18
                        assert val_type == numbers.Number

                        fmt = "{{:.{}g}}".format(loop_count+min_prec)
                        vstr = fmt.format(v)

                    else:
                        if loop_count == 0:
                            val_type = type(v)
                        assert isinstance(v, val_type)

                        # TODO optimize: fewer evaluations of vstr, remove
                        # common prefixes/suffixes over all vstr's
                        vstr = re.sub(r"\s+", " ", str(v)).strip()
                        vstr = re.sub(r"[^\w ,;.+-]+", "_", vstr)

                        if loop_count == 0: tracelog("vstr:", vstr)

                        if loop_count == 0:
                            max_loop = len(vstr) - min_prec

                        vstr = vstr[:loop_count + min_prec]

                    if vstr in strs:
                        # value string already present --> next attempt
                        break
                    else:
                        strs.add(vstr)
                        v2s[v] = vstr

            else:
                # for loop completed without break, i.e. the mapping for this
                # parameter is accepted
                value_map[p] = v2s
                break

            loop_count += 1
            if loop_count >= max_loop:
                errorlog("could not find unique string representation for the values of parameter {}".format(p))
                break

    debuglog("value_map", value_map)
    return value_map


def get_common_params(commits):
    keys = {}   # { param: set(values), ... }
    counts = {} # { param: count, ... }

    for co, par, _ in commits:
        for k, v in par.items():
            if k in keys:
                if v not in keys[k]:
                    keys[k].add(v)
                counts[k] += 1
            else:
                s = set()
                s.add(v)
                keys[k] = s
                counts[k] = 1

    ncom = len(commits)
    common_params = {}
    unique_params = set()

    for k, vals in keys.items():
        if len(vals) == 1 and counts[k] == ncom:
            for v in vals:
                common_params[k] = v
        else:
            unique_params.add(k)

    debuglog("common_params", common_params)
    debuglog("unique_params", unique_params)

    return common_params, unique_params


def open_repo(path):
    try:
        repo = git.Repository(path)
    except KeyError as e:
        fatallog("there is no git repository at {}".format(path))
        sys.exit(1)

    assert not repo.is_bare

    alt = os.path.join(repo.path, "objects/info/alternates")
    is_snapshot = os.path.exists(alt)

    if is_snapshot:
        debuglog("{} is a pampel snapshot".format(repo.workdir))

    return repo, is_snapshot


def open_main_repo(path):
    repo, is_snapshot = open_repo(path)

    # TODO read origin .pampel.json to detect if this is really a snapshot
    if is_snapshot:
        fatallog("{} is a pampel snapshot. I refuse to work on that.".format(repo.workdir))
        sys.exit(1)

    return repo


def process_check(args):
    repo = open_main_repo(args.repo[0])

    with PampelConfig(repo) as conf:
        changed = False

        naux = []
        for p in conf.aux_repos:
            debuglog("aux repo", p)
            try:
                git.Repository(p)
            except KeyError as e:
                warnlog("auxiliary repository {} does not exist.".format(p))
                changed = True
            else:
                naux.append(p)

        nsnap = []
        for p in conf.snapshots:
            debuglog("snapshot", p)
            try:
                git.Repository(p)
            except KeyError as e:
                warnlog("snapshot {} does not exist.".format(p))
                changed = True
            else:
                nsnap.append(p)

        if args.cleanup and changed:
            conf.aux_repos = naux
            conf.snapshots = nsnap

    # TODO auto track if conf changed
    if args.cleanup and changed:
        commit_conf(repo, conf)


def process_conf(args):
    repo = open_main_repo(args.repo[0])

    try:
        aux_repos = [ git.Repository(auxp) for auxp in args.aux_repo ]
    except KeyError as e:
        fatallog("could not access git repository:\n{}".format(e))
        sys.exit(1)

    with PampelConfig(repo) as conf:
        if len(aux_repos) != 0:
            infolog("setting auxiliary repositories")

            old_ars = list(conf.aux_repos)
            conf.aux_repos = [ a.workdir for a in aux_repos ]

            for a in aux_repos:
                if a.workdir not in old_ars:
                    infolog("new aux repo: {0}".format(a.workdir))
                else:
                    old_ars.remove(a.workdir)
            for a in old_ars:
                warnlog("removed aux repo: {0}".format(a))

        if len(args.command) != 0:
            if args.import_script: assert len(args.command) == 1

            infolog("changing command to be run")
            debuglog("{0} ({1}) --> {2} ({3})".format(
                " ".join(conf.command),
                "import" if conf.import_script else "run",
                " ".join(args.command),
                "import" if args.import_script else "run"
                ))
            conf.command = args.command
            conf.import_script = args.import_script

    commit_conf(repo, conf)


def commit_conf(repo, conf):
    conf.stage()
    tree = repo.index.write_tree()
    message = "pampel [conf]"
    repo.create_commit('HEAD', author, committer, message, tree, [ repo.head.peel().id ])


# TODO lenient only for aux repos
def process_rerun(args):
    repo, is_snapshot = open_repo(args.repo[0])
    args.test = is_snapshot

    for commit in repo.walk(repo.head.peel().id, git.GIT_SORT_TIME):
        m = pampel_commit_re.match(commit.message)
        if m:
            debuglog("last run is {}".format(commit.id))

            json_obj = commit_to_json(commit)
            cmdline = json_obj["run info"]["cmdline params"]

            if not isinstance(cmdline, list):
                warnlog("commandline is not provided as list. I will split it by myself.")
                cmdline = cmdline.split(" ")
            debuglog("cmdline", [ sys.argv[0] ] + cmdline[1:])

            old_args = parser.parse_args(cmdline[1:])    # TODO what if imported
            infolog("rerunning [#{}]:".format(m.group(1)),
                os.path.basename(sys.argv[0]), " ".join(cmdline[1:])
                )
            args.cmdline = [ sys.argv[0] ] + cmdline[1:] # TODO the params of parser_commmon are ignored
            args.args = old_args.args

            if args.dry_run: return


            process_run(args, repo, not is_snapshot)

            # print which files have changed
            chfs = [ f for f, s in repo.status().items()
                    if s != git.GIT_STATUS_IGNORED
                    and f != ".pampel.json"
                    and f != ".pampel-commit" ]
            if len(chfs) != 0:
                if args.ignore:
                    def ign(il, f):
                        for pat in il:
                            if fnmatch.fnmatch(f, pat): return True
                        return False
                    do_ign = [ ign(args.ignore, f) for f in chfs ]

                    igfs = [ f for i, f in enumerate(chfs) if do_ign[i] ]
                    chfs = [ f for i, f in enumerate(chfs) if not do_ign[i] ]
                else:
                    igfs = []

                if igfs:
                    infolog("Files that changed from previous run (ignored):\n" + "\n".join(sorted(igfs)))

                if chfs:
                    infolog("Files that changed from previous run:\n" + "\n".join(sorted(chfs)))
                else:
                    infolog("Rerun did not lead to any essential changes.")
                    infolog("Resetting repository to the last commit.")

                    repo.reset(repo.head.target, git.GIT_RESET_HARD)
                    commit = repo.head.peel()
                    # TODO add color
                    # modify exit status
                    infolog("HEAD now is at {} {}".format(str(commit.id)[:7], commit.message.split("\n",1)[0]))
            else:
                infolog("No files changed during the rerun.")

            if args.test and len(chfs) != 0:
                infolog("You can use `git diff' and `git status' to view changes between this and the previous run\n"
                        "and `git reset --hard' to discard the current changes.")

            return

    errorlog("did not find anything to be rerun")
    sys.exit(1)


def process_run(args, repo=None, do_commit=True):
    if repo is None:
        repo = open_main_repo(args.repo[0])

    # TODO warning when being lenient / ask for confirmation
    if args.lenient == 0:
        clean = is_repo_clean(repo)
        debuglog("repo {1}: {0}'".format(repo.workdir, ("clean" if clean else "dirty")))
    elif args.lenient == 1:
        clean = is_repo_clean_output(repo)
        debuglog("repo {1}: output dirs {0}'".format(repo.workdir, ("clean" if clean else "dirty")))
    else:
        # more lenient --> do not check
        clean = True

    if not clean:
        errorlog("Repository {0} is in a dirty state. " \
                "Please commit all your changes before running {1}.".format(repo.workdir, PROG))
        sys.exit(1)

    with PampelConfig(repo) as conf:
        aux_repos = [ git.Repository(auxp) for auxp in conf.aux_repos ]

        clean = True
        for r in aux_repos:
            clean = clean and is_repo_clean(r)
            if not clean:
                warnlog("Auxiliary repository `{}' is in a dirty state".format(r.workdir))
        if args.lenient < 2: assert clean

        conf.run_count += 1
        infolog("pampel run #{}".format(conf.run_count))

        if not args.contin: clear_output_dirs(repo)

        cmd = conf.command
        if conf.import_script:
            infolog("importing script {0}".format(cmd[0]))

            try:
                with _redirect_12():
                    script = imp.load_source("script", cmd[0])
            except Exception as e:
                fatallog("importing script {} failed:\n{}".format(cmd[0], e))
                raise e
            script_args = {}
            for kv in args.args:
                k, v = kv.split("=", 2)
                script_args[k] = v

            try:
                debuglog("init script")
                with _redirect_12():
                    script.init(script_args)

                infolog("running script")
                startts = datetime.datetime.now()
                with _redirect_12():
                    stat = script.run()
                endts = datetime.datetime.now()

                # getting parameters at the end, since they might change during
                # program execution
                infolog("getting parameters")
                with _redirect_12():
                    params = script.get_params()
            except Exception as e:
                errorlog("script threw exception: {}".format(e))
                raise e
        else:
            infolog("running command {0}".format(" ".join(cmd + args.args)))
            startts = datetime.datetime.now()
            with _redirect_12():
                stat = subprocess.call(cmd + args.args, cwd=repo.workdir)
            endts = datetime.datetime.now()

            if stat != 0:
                warnlog("command exited with status {0}".format(stat))

            infolog("getting parameters")
            # TODO add script params for get-params
            with _redirect_12():
                param_str = subprocess.check_output(cmd + [ "get-params" ] + args.args, cwd=repo.workdir)
            params = json.loads(param_str.decode("utf-8"))

    if not args.test: conf.stage()

    # generating commit message

    enc = JsonFormattedEncoder(-1)
    enc2 = JsonFormattedEncoder()

    enc2.start_obj()
    enc2.add_props_table([
        ("cmdline params", args.cmdline ),
        ("run count",      conf.run_count),
        None,
        ("command exit status", stat),
        ("start timestamp", startts),
        ("end timestamp", endts),
        ("time difference", endts-startts)
        ])
    enc2.end_obj()

    # info_json = str(enc2)

    enc.start_obj()
    enc.add_encoded_prop("run info", str(enc2))

    if aux_repos:
        json_ar = [
                { 
                    "path": a.workdir, # TODO change to .git path
                    "branch": "/".join(a.head.name.split("/")[2:]),
                    "commit": a.head.peel().id,
                    "dirty": not is_repo_clean(a)
                }
                for a in aux_repos
                ]

        enc.blank_line()
        enc.add_encoded_prop("aux repos", enc.encode(json_ar))

    enc2.reset()
    enc2.start_obj()
    enc2.add_props_table(sorted(params.items()))
    enc2.end_obj()

    enc.blank_line()
    enc.add_encoded_prop("params", str(enc2))

    enc.end_obj()

    message = "pampel [run #{}]\n\n".format(conf.run_count) + str(enc)

    debuglog(message)


    if do_commit:
        if args.lenient == 0 and not check_command_output(repo):
            errorlog("The command wrote something outside the output directories.\n"
                    "I will leave the I/O repo in the current state.\n"
                    "It is your responsibility to clean up the repo.")

            cfn = os.path.join(repo.workdir, ".pampel-commit")
            with open(cfn, "w") as cfh: cfh.write(message)
            infolog("Wrote the commit message to {0}".format(cfn))
        elif stat != 0:
            errorlog("The command finished with a nonzero status.\nI will not commit this run.")

            cfn = os.path.join(repo.workdir, ".pampel-commit")
            with open(cfn, "w") as cfh: cfh.write(message)
            infolog("Wrote the commit message to {0}".format(cfn))
        elif args.test:
            warnlog("I am in test mode. The current program run has not been committed.\n"
                    "If you go on you could possibly lose data.\n"
                    "To commit manually, use: {} commit".format(PROG))

            cfn = os.path.join(repo.workdir, ".pampel-commit")
            with open(cfn, "w") as cfh: cfh.write(message)
            infolog("Wrote the commit message to {0}".format(cfn))
        else:
            git_stage(repo)
            tree = repo.index.write_tree()
            oid = repo.create_commit('HEAD', author, committer, message, tree, [ repo.head.peel().id ])

        # TODO: print error message for duplicate tags
        # repo.create_tag("pampel-run-{0}".format(conf.run_count), oid, git.GIT_OBJ_COMMIT, committer, "")


def add_snapshot_multi(repo, args):
    snapp = args.snapshot
    newest_ref = args.to_ref[0]
    oldest_ref = args.from_ref[0]

    max_run = None
    min_run = None
    start_ref = None
    end_ref = None

    if newest_ref is None:
        start_ref = repo.head.target
    else:
        try:
            max_run = int(newest_ref)
        except ValueError:
            start_ref = repo.revparse_single(newest_ref).target
        else:
            start_ref = repo.head.target

    if oldest_ref is None:
        pass
    else:
        try:
            min_run = int(oldest_ref)
        except ValueError:
            end_ref = repo.revparse_single(oldest_ref).target
        else:
            pass

    # get pampel run commits
    if not args.any_branch:
        # build branch hierarchy
        # TODO stop if first effective branch point is found
        map_commit_ref = {}
        for refn in repo.listall_references():
            if refn.startswith("refs/heads/"):
                ref = repo.lookup_reference(refn)

                for commit in repo.walk(ref.peel().id, git.GIT_SORT_TIME):
                    m = pampel_commit_re.match(commit.message)
                    if m:
                        if max_run is not None and max_run < int(m.group(1)):
                            # skip commits which are too new
                            continue
                        if min_run is not None and min_run > int(m.group(1)):
                            # skip commits which are too old
                            break

                    if commit.id not in map_commit_ref:
                        map_commit_ref[commit.id] = []

                    map_commit_ref[commit.id].append(refn)
                    tracelog("{} -- {}".format(refn, commit.message.splitlines()[0]))

                    if m:
                        if min_run is not None and min_run == int(m.group(1)):
                            # skip commits which are too old
                            break

                    if commit.id == end_ref:
                        break


    commits = []
    curr_branch_refs = None

    has_old_bound = min_run is not None or end_ref is not None

    for commit in repo.walk(start_ref, git.GIT_SORT_TIME):
        m = pampel_commit_re.match(commit.message)
        if m:
            if max_run is not None and max_run < int(m.group(1)):
                # skip commits which are too new
                continue
            if min_run is not None and min_run > int(m.group(1)):
                # skip commits which are too old
                break

            if (not args.any_branch) and curr_branch_refs is None:
                # save refs of first commit that was not skipped
                curr_branch_refs = map_commit_ref[commit.id]

            json_obj = commit_to_json(commit)
            params = json_obj["params"]
            run_info = json_obj["run info"]
            commits.append((commit, params, run_info))

        if commit.id == end_ref:
            break

        if has_old_bound and (not args.any_branch) \
                and curr_branch_refs is not None \
                and map_commit_ref[commit.id] != curr_branch_refs:
            break

    common_params, unique_params = get_common_params(commits)

    info_content_dist = {}
    info_content = { "common parameters": common_params, "distinct parameters": info_content_dist }

    param_map = format_params(unique_params)

    # equivalence classes of same parameters
    classes = [] # list of tuples(params, [(commit, run_info)])

    for co, par, inf in commits:
        for cls in classes:
            if cls[0] == par:
                cls[1].append((co, inf))
                break
        else:
            tracelog("new class", inf["run count"], par)
            classes.append((par, [(co, inf)]))

    value_map = format_values(unique_params, [ c[0] for c in classes ])

    with PampelConfig(repo) as conf:
        new_repos = []

        for par, coms in classes:
            # choose latest commit from each class
            commit, run_info = max(coms, key=lambda c: c[0].commit_time)

            # get distinctive properties
            props = {}
            for k, v in par.items():
                if k not in common_params:
                    props[k] = v

            dirname = get_snapshot_dir(props, run_info, param_map, value_map)
            assert dirname not in info_content_dist
            info_content_dist[dirname] = props

            path = os.path.join(snapp, dirname)
            bn = "pampel-branch-{0}".format(run_info["run count"])
            conf.create_snapshot(path, commit, bn)
            
            # TODO add more info, like tag or run count
            new_repos.append(path)

    conf.stage()

    with open(os.path.join(snapp, "pampel-snap.json"), "w") as fh:
        json.dump(info_content, fh, indent=2, sort_keys=True)

    return new_repos


def add_snapshot_single(repo, args):
    snapp = args.snapshot

    new_repos = []
    branch_names = []
    commits = []

    for single_ref_s in args.ref:
        commit = None

        try:
            run_count   = int(single_ref_s)
            snap_dir    = "pampel-run-{:03}".format(run_count)
            branch_name = "pampel-branch-{}".format(run_count)
        except ValueError:
            # TODO better dir and branch names
            commit = repo.revparse_single(single_ref_s)
            snap_dir = single_ref_s
            branch_name = "pampel-branch-{}".format(single_ref_s)
        else:
            # search for commit with given run_count
            for cmt in repo.walk(repo.head.target, git.GIT_SORT_TIME):
                m = pampel_commit_re.match(cmt.message)
                if m:
                    if run_count == int(m.group(1)):
                        debuglog("{} -- {}".format(run_count, cmt.message.splitlines()[0]))
                        commit = cmt
                        break

                    if run_count == int(m.group(1)):
                        # skip commits which are too old
                        break

        assert commit is not None

        new_repos.append(os.path.join(snapp, snap_dir))
        branch_names.append(branch_name)
        commits.append(commit)


    with PampelConfig(repo) as conf:
        for path, bn, cmt in zip(new_repos, branch_names, commits):
            conf.create_snapshot(path, cmt, bn)
        # TODO add more info, like tag or run count
    conf.stage()

    return new_repos


# TODO also list and verify snapshots
def process_snap(args):
    repop = args.repo[0]

    repo = open_main_repo(repop)

    clean = is_repo_clean(repo)
    verblog("repo {1}: {0}'".format(repo.workdir, ("clean" if clean else "dirty")))
    # assert clean

    if args.action == "add":
        # TODO new param --subdirs

        if len(args.ref) != 0:
            # check arguments
            assert (not args.any_branch) \
                    and (not args.multi) \
                    and args.from_ref[0] is None \
                    and args.to_ref[0] is None

            # TODO let user choose exact output directory (not only parent dir)
            new_repos = [ add_snapshot_single(repo, args) ]
        else:
            new_repos = add_snapshot_multi(repo, args)

        message = "pampel [snap add]\n\n" \
                + json.dumps({ "paths": new_repos }, indent=2)

    elif args.action == "delete":
        # TODO handle pampel-snap.json specially
        with PampelConfig(repo) as conf:
            for snap in args.snapshots:
                if os.path.isdir(snap):
                    try:
                        conf.remove_snapshot(snap)
                    except git.GitError as e:
                        errorlog(e.message)
                    except KeyError:
                        pass
                    else:
                        infolog("snapshot {} removed".format(snap))
                else:
                    warnlog("{} is not a directory".format(snap))
        conf.stage()
        message = "pampel [snap delete]\n\n" \
                + json.dumps(args.snapshots, indent=2)
    else:
        raise ValueError("unknown action: {0}".format(args.action))

    debuglog(message)

    tree = repo.index.write_tree()
    repo.create_commit('HEAD', author, committer, message, tree, [ repo.head.peel().id ])


def process_comm(args):
    repop = args.repo[0]

    repo = git.Repository(repop)
    assert not repo.is_bare

    clean = is_repo_clean(repo)
    infolog("repo {1}: {0}'".format(repo.workdir, ("clean" if clean else "dirty")))

    # TODO add some error messages
    with open(os.path.join(repo.workdir, ".pampel-commit")) as cmf:
        msg_1st  = cmf.readline()
        msg_body = cmf.read()

    json_obj = json.loads(msg_body)
    run_count = json_obj["run info"]["run count"]

    git_stage(repo)
    tree = repo.index.write_tree()
    oid = repo.create_commit('HEAD', author, committer, msg_1st + msg_body, tree, [ repo.head.peel().id ])

    # TODO: print error message for duplicate tags
    repo.create_tag("pampel-run-{0}".format(run_count), oid, git.GIT_OBJ_COMMIT, committer, "")


def _run_main():
    global parser, _LOGLEVEL, _COLORED_OUTPUT

    parser = argparse.ArgumentParser(description="Keep track of program inputs and outputs")

    # common
    parser_common = argparse.ArgumentParser(description="Common options", add_help=False)

    parser_common.add_argument("--repo", "-r", nargs=1, help="git repository where changes are written to", default=["."])
    parser_common.add_argument("--verbose", "-v", action="count", help="be more verbose", default=_LOGLEVEL)
    parser_common.add_argument("--color", choices=["auto", "always", "never"], help="generate colored output", default="auto")


    subparsers = parser.add_subparsers(dest="subcommand", help="subcommands")
    subparsers.required = True

    
    # running commands
    parser_run = subparsers.add_parser("run", help="run a program", parents=[parser_common])

    parser_run.add_argument("--continue", "-c", action="store_true", help="do not clear output directories before running COMMAND", dest="contin")
    parser_run.add_argument("--lenient", "-l", action="count", help="complain less if the repository is not clean", default=0)
    parser_run.add_argument("--test", "-t", action="store_true", help="do not commit changes after run")
    parser_run.add_argument("args", help="arguments for the command to run", nargs="*", default=[])

    parser_run.set_defaults(func=process_run)


    # rerun last command
    parser_rerun = subparsers.add_parser("rerun", help="rerun command", parents=[parser_common])
    parser_rerun.add_argument("--continue", "-c", action="store_true", help="do not clear output directories before running COMMAND", dest="contin")
    parser_rerun.add_argument("--lenient", "-l", action="count", help="complain less if the repository is not clean", default=0)
    parser_rerun.add_argument("--test", "-t", action="store_true", help="do not commit changes after run")
    parser_rerun.add_argument("--ignore", action="append", help="ignore changes to matching paths")
    parser_rerun.add_argument("--dry-run", "-n", action="store_true", help="do not actually run, only print what would have ben run.")
    parser_rerun.set_defaults(func=process_rerun)


    # check
    parser_check = subparsers.add_parser("check", help="check configuration and repositories", parents=[parser_common])
    parser_check.add_argument("--cleanup", action="store_true", help="remove repositories which can not be found from the configuration file")
    parser_check.set_defaults(func=process_check)


    # config
    parser_conf = subparsers.add_parser("conf", help="set configuration options", parents=[parser_common])

    parser_conf.add_argument("--aux-repo", "-a", action="append", help="auxiliary git repositories, e.g., where source code sits", default=[])
    parser_conf.add_argument("--command", help="command to run", nargs="+", default=[])
    parser_conf.add_argument("--import", action="store_true", help="import command as a python script instead of running it as a new process", dest="import_script")

    parser_conf.set_defaults(func=process_conf)


    # snapshots
    parser_snap = subparsers.add_parser("snap", help="manage snapshots", parents=[parser_common])

    subparsers2 = parser_snap.add_subparsers(dest="action", help="action on snapshot")
    subparsers2.required = True
    
    parser_snap_add = subparsers2.add_parser("add", help="create shared git repo at the specified location", parents=[parser_common])
    parser_snap_add.add_argument("snapshot", metavar="SNAPSHOT_PATH")

    group_single = parser_snap_add.add_argument_group("single revision selection")
    group_single.add_argument("--ref", "-R", action="append", default=[], help="the revision to make a snapshof of")

    group_multi = parser_snap_add.add_argument_group("multiple revision selection")
    group_multi.add_argument("--from", nargs=1, default=[None], dest="from_ref", help="oldest revision of which a snapshot is made")
    group_multi.add_argument("--to",   nargs=1, default=[None], dest="to_ref", help="newest revision of which a snapshot is made")
    group_multi.add_argument("--any-branch", action="store_true", help="look for matching revisions in any branch")
    group_multi.add_argument("--multi", action="store_true", help="select multiple revisions to make snapshots of")

    parser_snap_del = subparsers2.add_parser("delete", help="delete shared git repo at the specified location", parents=[parser_common])
    parser_snap_del.add_argument("snapshots", metavar="SNAPSHOT_PATH", nargs="+")

    parser_snap.set_defaults(func=process_snap)


    # commit
    parser_comm = subparsers.add_parser("commit", help="commit changes", parents=[parser_common])
    parser_comm.set_defaults(func=process_comm)


    args = parser.parse_args()

    _LOGLEVEL = args.verbose
    _COLORED_OUTPUT = args.color

    args.cmdline = sys.argv

    args.func(args)


if __name__ == "__main__":
    _run_main()

