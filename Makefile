# (Abusive?) simplification of the Makefile suggested in Coq Manual (may 2024)

KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: $(KNOWNFILES)
	$(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(MAKECMDGOALS)

.PHONY: invoke-coqmakefile $(KNOWNFILES)

%: invoke-coqmakefile
	@true
