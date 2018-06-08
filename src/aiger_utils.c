//
//  aiger_utils.c
//  cadet
//
//  Created by Markus Rabe on 10/11/2016.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "aiger_utils.h"
#include "log.h"

#include <assert.h>

int aiger_lit2lit(unsigned aigerlit, int truelit) {
    if (aigerlit == aiger_true) {
        assert(truelit != 0);
        return truelit;
    }
    if (aigerlit == aiger_false) {
        assert(truelit != 0);
        return -truelit;
    }
    int var = aiger_lit2var(aigerlit);
    assert(var != 0);
    int res = aigerlit % 2 ? - var : var;
    assert(abs(res) != abs(truelit));
    return res;
}

unsigned inc(unsigned* sym) {
    *sym += 2;
    return *sym;
}

bool is_negated(unsigned signal) {
    return signal % 2; // negation is encoded in the last bit
}

// Negates aiger signals
unsigned negate(unsigned signal) {
    return signal ^ 1; // flipping the last bit with xor
}

unsigned var2aigerlit(unsigned var_id) {
    return 2 * var_id;
}

unsigned aigeru_multiAND(aiger* a, unsigned* max_sym, int_vector* input_aigerlits) {
    unsigned outputlit = inc(max_sym);
    aigeru_add_multiAND(a, max_sym, outputlit, input_aigerlits);
    return outputlit;
}

void aigeru_add_multiAND(aiger* a, unsigned* max_sym, unsigned output_aigerlit, int_vector* input_aigerlits) {
    assert(!is_negated(output_aigerlit));
    if (int_vector_count(input_aigerlits) == 0) {
        aiger_add_and(a, output_aigerlit, aiger_true, aiger_true); // empty AND is true
        return;
    }
    unsigned cur_output = aiger_true;
    for (unsigned i = 0; i < int_vector_count(input_aigerlits) - 1; i++) {
        unsigned input_aigerlit = (unsigned) int_vector_get(input_aigerlits, i);
        cur_output = aigeru_AND(a, max_sym, cur_output, input_aigerlit);
    }
    unsigned last_lit = (unsigned) int_vector_get(input_aigerlits, int_vector_count(input_aigerlits) - 1);
    aiger_add_and(a, output_aigerlit, cur_output, last_lit);
}

//void aigeru_add_multiAND(aiger* a, unsigned* max_sym, unsigned output_aigerlit, int_vector* input_aigerlits) {
//    assert(!is_negated(output_aigerlit));
//    if (int_vector_count(input_aigerlits) == 0) {
//        aiger_add_and(a, output_aigerlit, aiger_true, aiger_true); // empty AND is true
//        return;
//    }
//    if (int_vector_count(input_aigerlits) == 1) {
//        unsigned last_lit = (unsigned) int_vector_get(input_aigerlits, 0);
//        aiger_add_and(a, output_aigerlit, last_lit, last_lit); // empty AND is true
//        return;
//    }
//    assert(int_vector_count(input_aigerlits) >= 2); // can define a proper AND
//    unsigned cur_outputlit = output_aigerlit;
//    for (unsigned i = 0; i < int_vector_count(input_aigerlits) - 2; i++) {
//        unsigned input_aigerlit = (unsigned) int_vector_get(input_aigerlits, i);
//        unsigned next_outputlit = inc(max_sym);
//        aiger_add_and(a, cur_outputlit, next_outputlit, input_aigerlit);
//        cur_outputlit = next_outputlit;
//    }
//    unsigned last_lit = (unsigned) int_vector_get(input_aigerlits, int_vector_count(input_aigerlits) - 1);
//    unsigned second_to_last_lit = (unsigned) int_vector_get(input_aigerlits, int_vector_count(input_aigerlits) - 2);
//    aiger_add_and(a, cur_outputlit, last_lit, second_to_last_lit);
//}

void aigeru_add_OR(aiger* a, unsigned* max_sym, unsigned output_aigerlit, unsigned i1, unsigned i2) {
    unsigned negated_outputlit = 0;
    if (is_negated(output_aigerlit)) {
        negated_outputlit = negate(output_aigerlit);
    } else {
        negated_outputlit = inc(max_sym);
        aiger_add_and(a, output_aigerlit, negate(negated_outputlit), negate(negated_outputlit));
    }
    aiger_add_and(a, negated_outputlit, negate(i1), negate(i2));
}

unsigned aigeru_OR(aiger* a, unsigned* max_sym, unsigned i1, unsigned i2) {
    return negate(aigeru_AND(a, max_sym, negate(i1), negate(i2)));
}

unsigned aigeru_AND(aiger* a, unsigned* max_sym, unsigned i1, unsigned i2) {
    if (i1 == aiger_true) {
        return i2;
    }
    if (i2 == aiger_true) {
        return i1;
    }
    if (i1 == aiger_false || i2 == aiger_false) {
        return aiger_false;
    }
    if (i1 == i2) {
        return i1;
    }
    if (i1 == negate(i2)) {
        return aiger_false;
    }
    unsigned out = inc(max_sym);
    aiger_add_and(a, out, i1, i2);
    return out;
}

unsigned aigeru_multiOR(aiger* a, unsigned* max_sym, int_vector* input_aigerlits) {
    unsigned outputlit = aiger_false;
    for (unsigned i = 0; i < int_vector_count(input_aigerlits); i++) {
        outputlit = aigeru_OR(a, max_sym, outputlit, (unsigned) int_vector_get(input_aigerlits, i));
    }
    return outputlit;
}

void aigeru_add_multiOR(aiger* a, unsigned* max_sym, unsigned output_aigerlit, int_vector* input_aigerlits) {
    unsigned negated_outputlit = 0;
    if (is_negated(output_aigerlit)) {
        negated_outputlit = negate(output_aigerlit);
    } else {
        negated_outputlit = inc(max_sym);
        aiger_add_and(a, output_aigerlit, negate(negated_outputlit), negate(negated_outputlit));
    }
    int_vector* negated_inputlits = int_vector_init();
    for (unsigned i = 0; i < int_vector_count(input_aigerlits); i++) {
        int_vector_add(negated_inputlits, (int) negate((unsigned) int_vector_get(input_aigerlits, i)));
    }
    aigeru_add_multiAND(a, max_sym, negated_outputlit, negated_inputlits);
    int_vector_free(negated_inputlits);
}


void aigeru_add_multiplexer(aiger* a, unsigned* max_sym, unsigned output,
                               unsigned selector, unsigned if_signal, unsigned else_signal) {
    LOG_WARNING("Not sure if this component is correct.");
    unsigned if_component = inc(max_sym);
    aiger_add_and(a, if_component, selector, if_signal);
    unsigned else_component = inc(max_sym);
    aiger_add_and(a, else_component, negate(selector), else_signal);
    unsigned negation_of_output = inc(max_sym); // need extra symbol as we cannot define left side of the final and as negated signal.
    aiger_add_and(a, negation_of_output, negate(if_component), negate(else_component));
    aiger_add_and(a, output, negate(negation_of_output), negate(negation_of_output));
}

unsigned aigeru_MUX(aiger* a, unsigned* max_sym, unsigned selector, unsigned i1, unsigned i2) {
    unsigned i1_out = aigeru_AND(a, max_sym, selector, i1);
    unsigned i2_out = aigeru_AND(a, max_sym, negate(selector), i2);
    return aigeru_OR(a, max_sym, i1_out, i2_out);
}


unsigned aigeru_multiMUX(aiger* a, unsigned* max_sym, int_vector* selectors, int_vector* inputs) {
    assert(int_vector_count(selectors) == int_vector_count(inputs));
    unsigned out = aiger_false;
    unsigned previous_case_applies = aiger_false;
    for (unsigned i = 0; i < int_vector_count(selectors); i++) {
        unsigned selector = (unsigned) int_vector_get(selectors, i);
        unsigned value = (unsigned) int_vector_get(inputs, i);
        unsigned this_case_applies = aigeru_AND(a, max_sym, negate(previous_case_applies), selector);
        unsigned selected_value = aigeru_AND(a, max_sym, this_case_applies, value);
        out = aigeru_OR(a, max_sym, out, selected_value);
        if (i + 1 < int_vector_count(selectors)) {
            previous_case_applies = aigeru_OR(a, max_sym, previous_case_applies, selector);
        }
    }
    return out;
}
