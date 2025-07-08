Definition imported := 1 + 1.

(* Observe the _CoqProject file
    -Q . TEST
maps the current (wrt the _CoqProject file), physical directory to the logical directory "TEST"


With the _CoqProject file

    coq_makefile -f _CoqProject *.v -o Makefile

    make Sub.vo

*)

Module Type T.
  Parameter n : nat.
  Notation bob := n.
End         T.









(* From Software Foundations: Look into the 2nd chpt, because that will require compiling the first chapter *)


(*

Before getting started on this chapter, we need to import all of our definitions from the previous chapter:
From LF Require Export Basics.
For this Require command to work, Coq needs to be able to find a compiled version of the previous chapter (Basics.v). This compiled version, called Basics.vo, is analogous to the .class files compiled from .java source files and the .o files compiled from .c files.
To compile Basics.v and obtain Basics.vo, first make sure that the files Basics.v, Induction.v, and _CoqProject are in the current directory.
The _CoqProject file should contain just the following line:
      -Q . LF
This maps the current directory (".", which contains Basics.v, Induction.v, etc.) to the prefix (or "logical directory") "LF". Proof General, CoqIDE, and VSCoq read _CoqProject automatically, to find out to where to look for the file Basics.vo corresponding to the library LF.Basics.
Once the files are in place, there are various ways to build Basics.vo from an IDE, or you can build it from the command line. From an IDE... 

To compile Basics.v from the command line...

    First, generate a Makefile using the coq_makefile utility, which comes installed with Coq. (If you obtained the whole volume as a single archive, a Makefile should already exist and you can skip this step.)
             coq_makefile -f _CoqProject *.v -o Makefile
    You should rerun that command whenever you add or remove Coq files in this directory.
    Now you can compile Basics.v by running make with the corresponding .vo file as a target:
             make Basics.vo
    All files in the directory can be compiled by giving no arguments:
             make
    Under the hood, make uses the Coq compiler, coqc. You can also run coqc directly:
             coqc -Q . LF Basics.v
    Since make also calculates dependencies between source files to compile them in the right order, make should generally be preferred over running coqc explicitly. But as a last (but not terrible) resort, you can simply compile each file manually as you go. For example, before starting work on the present chapter, you would need to run the following command:
            coqc -Q . LF Basics.v
    Then, once you've finished this chapter, you'd do
            coqc -Q . LF Induction.v
    to get ready to work on the next one. If you ever remove the .vo files, you'd need to give both commands again (in that order).

Troubleshooting:

    For many of the alternatives above you need to make sure that the coqc executable is in your PATH.
    If you get complaints about missing identifiers, it may be because the "load path" for Coq is not set up correctly. The Print LoadPath. command may be helpful in sorting out such issues.
    When trying to compile a later chapter, if you see a message like
            Compiled library Induction makes inconsistent assumptions over
            library Basics
    a common reason is that the library Basics was modified and recompiled without also recompiling Induction which depends on it. Recompile Induction, or everything if too many files are affected (for instance by running make and if even this doesn't work then make clean; make).
    If you get complaints about missing identifiers later in this file it may be because the "load path" for Coq is not set up correctly. The Print LoadPath. command may be helpful in sorting out such issues.
    In particular, if you see a message like
               Compiled library Foo makes inconsistent assumptions over
               library Bar
    check whether you have multiple installations of Coq on your machine. It may be that commands (like coqc) that you execute in a terminal window are getting a different version of Coq than commands executed by Proof General or CoqIDE.
    One more tip for CoqIDE users: If you see messages like Error: Unable to locate library Basics, a likely reason is inconsistencies between compiling things within CoqIDE vs using coqc from the command line. This typically happens when there are two incompatible versions of coqc installed on your system (one associated with CoqIDE, and one associated with coqc from the terminal). The workaround for this situation is compiling using CoqIDE only (i.e. choosing "make" from the menu), and avoiding using coqc directly at all.
    
*)
