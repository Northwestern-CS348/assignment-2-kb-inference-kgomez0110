import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

   
    def retract_helper(self, fact_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_rule])
        ####################################################
        # Student code goes here
        
        # TODO: Check if it's a rule or a fact
        isFact = isinstance(fact_rule, Fact)

        # TODO: If fact - check if it's in the kb. then check if it's supported by anything.
        if isFact:
            fact = self._get_fact(fact_rule)
            if fact:
                if len(fact.supported_by) == 0:
                    if fact.supports_facts:
                        for f in fact.supports_facts:
                            ## for each fact it supports, remove it from their supported list
                            if f.supported_by:
                                for fs in f.supported_by:
                                    if (fs[0] == fact):
                                        f.supported_by.remove(fs)
                                ## if it was the only fact that supported it, retract that fact too
                            if len(f.supported_by) == 0: 
                                self.retract_helper(f)
                        
                    ## pretty much the same thing for rules
                    if fact.supports_rules:
                        for r in fact.supports_rules:
                            if r.supported_by:
                                for rs in r.supported_by:
                                    if (rs[0] == fact):
                                        r.supported_by.remove(rs)
                            if (len(r.supported_by) == 0 and (not r.asserted)):
                                self.retract_helper(r)
                    # then remove fact
                    self.facts.remove(fact)


        # TODO: If rule -
        ## if it isnt asserted and nothing supportes it
        ## for each fact that rule supports, check that facts supported by and delete the fact we're retracting
        ## if it was the only one, retract the iterating fact
        ## same thing for rules
        ## remove rule

        else:
            rule = self._get_rule(fact_rule)
            if len(rule.supported_by) == 0:
                if rule.supports_facts:
                    for f in rule.supports_facts:
                        ## for each fact it supports, remove it from their supported list
                        if f.supported_by:
                            for fs in f.supported_by:
                                if (fs[1] == rule):
                                    f.supported_by.remove(fs)
                        ## if it was the only fact that supported it, retract that fact too
                        if len(f.supported_by) == 0:
                            self.retract_helper(f)
                    
                ## pretty much the same thing for rules
                if rule.supports_rules:
                    for r in rule.supports_rules:
                        if r.supported_by:
                            for rs in r.supported_by:
                                if (rs[1] == rule):
                                    r.supported_by.remove(rs)
                        if (len(r.supported_by) == 0 and (not r.asserted)):
                            self.retract_helper(r)
                # then remove fact
                self.rules.remove(rule)

    def kb_retract(self, fact):
        if isinstance(fact, Fact):
            self.retract_helper(fact)      

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])

        first_statement = rule.lhs[0]
        bindings = match(fact.statement, first_statement)
        if (bindings):
            if (len(rule.lhs) == 1):
                statement = instantiate(rule.rhs, bindings)
                fr = Fact(statement, [[fact, rule]])
                fact.supports_facts.append(fr)
                rule.supports_facts.append(fr)
                kb.kb_assert(fr)
            else:
                rules = []
                for statement in rule.lhs[1:]:
                    rules.append(instantiate(statement, bindings))
                fr = Rule([rules, instantiate(rule.rhs, bindings)], [[fact, rule]])
                fact.supports_rules.append(fr)
                rule.supports_rules.append(fr)
                kb.kb_assert(fr)

        ####################################################
        # Student code goes here

    

        

