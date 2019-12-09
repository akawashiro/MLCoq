theories/Tactics/Tactics.vo theories/Tactics/Tactics.glob theories/Tactics/Tactics.v.beautified: theories/Tactics/Tactics.v src/lib/hammer_lib$(DYNLIB) src/tactics/hammer_tactics$(DYNOBJ)
theories/Tactics/Tactics.vio: theories/Tactics/Tactics.v src/lib/hammer_lib$(DYNLIB) src/tactics/hammer_tactics$(DYNOBJ)
theories/Tactics/Reconstr.vo theories/Tactics/Reconstr.glob theories/Tactics/Reconstr.v.beautified: theories/Tactics/Reconstr.v
theories/Tactics/Reconstr.vio: theories/Tactics/Reconstr.v
theories/Plugin/Hammer.vo theories/Plugin/Hammer.glob theories/Plugin/Hammer.v.beautified: theories/Plugin/Hammer.v theories/Tactics/Reconstr.vo theories/Tactics/Tactics.vo src/plugin/hammer_plugin$(DYNOBJ)
theories/Plugin/Hammer.vio: theories/Plugin/Hammer.v theories/Tactics/Reconstr.vio theories/Tactics/Tactics.vio src/plugin/hammer_plugin$(DYNOBJ)
