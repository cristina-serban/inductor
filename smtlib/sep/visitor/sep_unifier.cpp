#include "sep_unifier.h"
#include "sep_duplicator.h"
#include "sep_term_replacer.h"

#include <sstream>

using namespace std;
using namespace smtlib::sep;

string Equality::toString() {
    stringstream ss;
    ss << first->toString() << " " << second->toString();
    return ss.str();
}

void UnifierContext::merge(vector<Equality> eqs) {
    this->eqs.insert(this->eqs.end(), eqs.begin(), eqs.end());
}

bool Unifier::unify(sptr_t<Term> node) {
    unified = true;

    if (node->toString() != ctx->getTerm()->toString()) {
        sptr_t<Duplicator> duplicator = make_shared<Duplicator>();

        vector<Equality> used;
        unordered_map<string, bool> replaced;

        bool finished = false;
        while (!finished) {
            visit0(node);

            if(!unified) {
                finished = true;
                break;
            }

            sptr_t<Term> dupNode = dynamic_pointer_cast<Term>(duplicator->run(node));
            sptr_t<Term> dupTerm = dynamic_pointer_cast<Term>(duplicator->run(ctx->getTerm()));
            ctx->setTerm(dupTerm);

            long size = ctx->getEqualities().size();
            for(long i = 0; i < size; i++) {
                auto first = ctx->getEqualities()[i].first;
                auto second = ctx->getEqualities()[i].second;

                sptr_t<TermReplacer> replacer;

                if(dynamic_pointer_cast<SimpleIdentifier>(first)
                   && replaced.end() == replaced.find(first->toString())) {
                    replacer = make_shared<TermReplacer>(make_shared<TermReplacerContext>(first, second));
                    replaced[first->toString()] = true;
                } else if(dynamic_pointer_cast<SimpleIdentifier>(second)
                          && replaced.end() == replaced.find(second->toString())) {
                    replacer = make_shared<TermReplacer>(make_shared<TermReplacerContext>(second, first));
                    replaced[second->toString()] = true;
                }

                if(replacer) {
                    dupNode = replacer->run(dupNode);
                    dupTerm = replacer->run(dupTerm);

                    used.push_back(ctx->getEqualities()[i]);
                    ctx->getEqualities().erase(ctx->getEqualities().begin() + i);
                    i--;
                    size--;
                }
            }

            node = dupNode;
            ctx->setTerm(dupTerm);

            if(node->toString() == ctx->getTerm()->toString()) {
                finished = true;
            }
        }

        ctx->getSubstitution().insert(ctx->getSubstitution().end(), used.begin(), used.end());
    }
    return unified;
}

void Unifier::visit(sptr_t<SimpleIdentifier> node) {
    ctx->getEqualities().push_back(Equality(node, ctx->getTerm()));
}

void Unifier::visit(sptr_t<QualifiedIdentifier> node) {
    if (auto qid = dynamic_pointer_cast<QualifiedIdentifier>(ctx->getTerm())) {
        // TODO Properly check sort
        if (node->sort->toString() == qid->sort->toString()) {
            ctx->getEqualities().push_back(Equality(node->identifier, qid->identifier));
        } else {
            unified = false;
        }
    } else {
        ctx->getEqualities().push_back(Equality(node, ctx->getTerm()));
    }
}

void Unifier::visit(sptr_t<DecimalLiteral> node) {
    if (auto dec = dynamic_pointer_cast<DecimalLiteral>(ctx->getTerm())) {
        if (dec->value != dec->value)
            unified = false;
    } else {
        ctx->getEqualities().push_back(Equality(node, ctx->getTerm()));
    }
}

void Unifier::visit(sptr_t<NumeralLiteral> node) {
    if (auto num = dynamic_pointer_cast<NumeralLiteral>(ctx->getTerm())) {
        if (num->value != num->value)
            unified = false;
    } else {
        ctx->getEqualities().push_back(Equality(node, ctx->getTerm()));
    }
}

void Unifier::visit(sptr_t<StringLiteral> node) {
    if (auto str = dynamic_pointer_cast<StringLiteral>(ctx->getTerm())) {
        if (str->value != str->value)
            unified = false;
    } else {
        ctx->getEqualities().push_back(Equality(node, ctx->getTerm()));
    }
}

void Unifier::visit(sptr_t<QualifiedTerm> node) {
    if (auto qterm = dynamic_pointer_cast<QualifiedTerm>(ctx->getTerm())) {
        auto sid1 = dynamic_pointer_cast<SimpleIdentifier>(node->identifier);
        auto sid2 = dynamic_pointer_cast<SimpleIdentifier>(qterm->identifier);
        auto qid1 = dynamic_pointer_cast<QualifiedIdentifier>(node->identifier);
        auto qid2 = dynamic_pointer_cast<QualifiedIdentifier>(qterm->identifier);

        if ((sid1 && sid2 && sid1->name != sid2->name)
            || (sid1 && qid2 && sid1->name != qid2->identifier->name)
            || (qid1 && sid2 && qid1->identifier->name != sid2->name)
            || (qid1 && qid2 && qid1->identifier->name != qid2->identifier->name)) {
            unified = false;
            return;
        }

        auto terms1 = node->terms;
        auto terms2 = qterm->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());
        }
    } else if(!dynamic_pointer_cast<SimpleIdentifier>(ctx->getTerm())
              || !dynamic_pointer_cast<QualifiedIdentifier>(ctx->getTerm())) {
        unified = false;
    } else {
        ctx->getEqualities().push_back(Equality(node, ctx->getTerm()));
    }
}

void Unifier::visit(sptr_t<LetTerm> node) {
    // TODO
}

void Unifier::visit(sptr_t<ForallTerm> node) {
    // TODO
}

void Unifier::visit(sptr_t<ExistsTerm> node) {
    if (auto term = dynamic_pointer_cast<ExistsTerm>(ctx->getTerm())) {
        if(node->bindings.size() == term->bindings.size()) {
            for(size_t i = 0, n = node->bindings.size(); i < n; i++) {
                sptr_t<SimpleIdentifier> id1 = make_shared<SimpleIdentifier>(node->bindings[i]->name);
                sptr_t<SimpleIdentifier> id2 = make_shared<SimpleIdentifier>(term->bindings[i]->name);
                ctx->getEqualities().push_back(Equality(id1, id2));
            }

            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(term->term);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(node->term);
            ctx->merge(newCtx->getSubstitution());

            if (!unified)
                return;
        } else {
            unified = false;
        }
    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<MatchTerm> node) {
    // TODO
}

void Unifier::visit(sptr_t<AnnotatedTerm> node) {
    visit0(node->term);
}

void Unifier::visit(sptr_t<TrueTerm> node) {
    if (auto term = dynamic_pointer_cast<TrueTerm>(ctx->getTerm())) {
        return;
    } else if (auto var = dynamic_pointer_cast<SimpleIdentifier>(ctx->getTerm())) {
        ctx->getEqualities().push_back(Equality(node, var));
    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<FalseTerm> node) {
    if (auto term = dynamic_pointer_cast<FalseTerm>(ctx->getTerm())) {
        return;
    } else if (auto var = dynamic_pointer_cast<SimpleIdentifier>(ctx->getTerm())) {
        ctx->getEqualities().push_back(Equality(node, var));
    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<NotTerm> node) {
    if (auto term = dynamic_pointer_cast<NotTerm>(ctx->getTerm())) {
        sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(term->term);
        sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
        unified = newUnifier->unify(node->term);
        ctx->merge(newCtx->getSubstitution());
    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<ImpliesTerm> node) {
    if (auto term = dynamic_pointer_cast<ImpliesTerm>(ctx->getTerm())) {
        auto terms1 = node->terms;
        auto terms2 = term->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());
        }

    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<AndTerm> node) {
    if (auto term = dynamic_pointer_cast<AndTerm>(ctx->getTerm())) {
        auto terms1 = node->terms;
        auto terms2 = term->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());
        }

    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<OrTerm> node) {
    if (auto term = dynamic_pointer_cast<OrTerm>(ctx->getTerm())) {
        auto terms1 = node->terms;
        auto terms2 = term->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());
        }

    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<XorTerm> node) {
    if (auto term = dynamic_pointer_cast<XorTerm>(ctx->getTerm())) {
        auto terms1 = node->terms;
        auto terms2 = term->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());

            if (!unified)
                return;
        }

    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<EqualsTerm> node) {
    if (auto term = dynamic_pointer_cast<EqualsTerm>(ctx->getTerm())) {
        auto terms1 = node->terms;
        auto terms2 = term->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());

            if (!unified)
                return;
        }

    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<DistinctTerm> node) {
    if (auto term = dynamic_pointer_cast<DistinctTerm>(ctx->getTerm())) {
        auto terms1 = node->terms;
        auto terms2 = term->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());

            if (!unified)
                return;
        }

    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<IteTerm> node) {
    if (auto term = dynamic_pointer_cast<IteTerm>(ctx->getTerm())) {
        sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(term->testTerm);
        sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
        unified = newUnifier->unify(node->testTerm);
        ctx->merge(newCtx->getSubstitution());

        if (!unified)
            return;

        newCtx->getEqualities().clear();
        newCtx->setTerm(term->thenTerm);
        unified = newUnifier->unify(node->thenTerm);
        ctx->merge(newCtx->getSubstitution());

        if (!unified)
            return;

        newCtx->getEqualities().clear();
        newCtx->setTerm(term->elseTerm);
        unified = newUnifier->unify(node->elseTerm);
        ctx->merge(newCtx->getSubstitution());
    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<EmpTerm> node) {
    if (!dynamic_pointer_cast<EmpTerm>(ctx->getTerm()))
        unified = false;
}

void Unifier::visit(sptr_t<SepTerm> node) {
    if (auto term = dynamic_pointer_cast<SepTerm>(ctx->getTerm())) {
        auto terms1 = node->terms;
        auto terms2 = term->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());

            if (!unified)
                return;
        }

    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<WandTerm> node) {
    if (auto term = dynamic_pointer_cast<WandTerm>(ctx->getTerm())) {
        auto terms1 = node->terms;
        auto terms2 = term->terms;
        long size = node->terms.size();

        if (size != terms2.size()) {
            unified = false;
            return;
        }

        for (long i = 0; i < size; i++) {
            sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(terms2[i]);
            sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
            unified = newUnifier->unify(terms1[i]);
            ctx->merge(newCtx->getSubstitution());

            if (!unified)
                return;
        }

    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<PtoTerm> node) {
    if (auto term = dynamic_pointer_cast<PtoTerm>(ctx->getTerm())) {
        sptr_t<UnifierContext> newCtx = make_shared<UnifierContext>(term->leftTerm);
        sptr_t<Unifier> newUnifier = make_shared<Unifier>(newCtx);
        unified = newUnifier->unify(node->leftTerm);
        ctx->merge(newCtx->getSubstitution());

        if (!unified)
            return;

        newCtx->getEqualities().clear();
        newCtx->setTerm(term->rightTerm);
        unified = newUnifier->unify(node->rightTerm);
        ctx->merge(newCtx->getSubstitution());
    } else {
        unified = false;
    }
}

void Unifier::visit(sptr_t<NilTerm> node) {
    // TODO check sorts

    if (auto var = dynamic_pointer_cast<SimpleIdentifier>(ctx->getTerm())) {
        ctx->getEqualities().push_back(Equality(node, var));
    } else {
        unified = false;
    }
}