SHELL := /bin/bash

TLAPM := time tlapm --nofp

TLA2TOOLS ?= $(HOME)/bin/tla2tools.jar
TLAPS_LIB = $(shell tlapm --where)
TLC = java -XX:+UseParallelGC -DTLA-Library="$(TLAPS_LIB)" -jar "$(TLA2TOOLS)"
CFG ?= $(MC)

all: agreement termination

agreement:
	$(TLAPM) TendermintVotingProofs.tla
	$(TLAPM) TendermintOperationalRefinement.tla
	$(TLAPM) TendermintByzantineRefinement.tla
	$(TLAPM) TendermintPartialSyncRefinement.tla

termination: term-base term-nonzeno term-within term-roundprog term-selection \
	term-crossround term-dominator term-cascade-inv term-cascade-region \
	term-cascade-core term-cascade term-lockretry term-comp

term-base: ; $(TLAPM) TendermintPartialSyncTerminationBase.tla
term-nonzeno: ; $(TLAPM) TendermintPartialSyncTerminationNonZeno.tla
term-within: ; $(TLAPM) TendermintPartialSyncTerminationWithinRound.tla
term-crossround: ; $(TLAPM) TendermintPartialSyncTerminationCrossRound.tla
term-dominator: ; $(TLAPM) TendermintPartialSyncTerminationDominator.tla
term-roundprog: ; $(TLAPM) TendermintPartialSyncTerminationRoundProgress.tla
term-selection: ; $(TLAPM) TendermintPartialSyncTerminationSelection.tla
term-cascade-inv: ; $(TLAPM) TendermintPartialSyncTerminationCascadeInvariants.tla
term-cascade-region: ; $(TLAPM) TendermintPartialSyncTerminationCascadeRegion.tla
term-cascade-core: ; $(TLAPM) TendermintPartialSyncTerminationCascadeCore.tla
term-cascade: ; $(TLAPM) TendermintPartialSyncTerminationCascade.tla
term-lockretry: ; $(TLAPM) TendermintPartialSyncTerminationLockRetry.tla
term-comp: ; $(TLAPM) TendermintPartialSyncTermination.tla

tlc:
	@[ -n "$(MC)" ] || { echo 'usage: make tlc MC=<module> [CFG=<config>]   names carry no extension'; exit 2; }
	@[ -r "$(TLA2TOOLS)" ] || { echo 'cannot read $(TLA2TOOLS); set TLA2TOOLS=/path/to/tla2tools.jar'; exit 2; }
	$(TLC) -config $(CFG).cfg $(MC).tla

.PHONY: all agreement termination tlc \
	term-base term-nonzeno term-within term-roundprog term-selection \
	term-crossround term-dominator term-cascade-inv term-cascade-region \
	term-cascade-core term-cascade term-lockretry term-comp
