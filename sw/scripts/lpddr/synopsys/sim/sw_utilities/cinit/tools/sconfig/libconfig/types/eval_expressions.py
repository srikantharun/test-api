#!/usr/bin/env python3
# -------------------------------------------------------------------------------
# 
# Copyright 2024 Synopsys, INC.
# 
# This Synopsys IP and all associated documentation are proprietary to
# Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
# written license agreement with Synopsys, Inc. All other use, reproduction,
# modification, or distribution of the Synopsys IP or the associated
# documentation is strictly prohibited.
# Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
#            Inclusivity and Diversity" (Refer to article 000036315 at
#                        https://solvnetplus.synopsys.com)
# 
# Component Name   : DWC_ddrctl_lpddr54
# Component Version: 1.60a-lca00
# Release Type     : LCA
# Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
# -------------------------------------------------------------------------------


# System
import re
from abc import abstractmethod

# Local
from libconfig.log import Log

class EvalExpressionsError(Exception):
    def __init__(self, message, expression):
        if isinstance(expression, list) is True:
            self.expression = " ".join([str(token) for token in expression])
        else:
            self.expression = expression
        super().__init__(message)

    def __str__(self):
        return super().__str__() + "\nExpression: %s" % self.expression

class EvalExpressions:

    def evaluate(expression, config_dict=None, static_only=False):
        """ evaluate an expression based on data from config_dict """

        expression_alt = EvalExpressions.sanitize(expression)
        expression_tokens = EvalExpressions.tokenize(expression_alt)
        if (config_dict is not None):
            expression_tokens = EvalExpressions.replace_params(expression_tokens, config_dict, static_only=static_only)

        expression_result = EvalExpressions.solve(expression_tokens)

        Log().debug("Evaluate \"%s\" : \"%s\" : \"%s\"" % (expression, expression_tokens, expression_result))
        return expression_result

    def evaluate_to_int(expression, config_dict=None, static_only=False):
        """ Evaluate expression """

        return int(EvalExpressions.evaluate(expression, config_dict, static_only=static_only))

    def sanitize(expression):
        """ Sanitize expression """
        expression = expression.replace(' AND ', '&&').replace(' OR ', '||')
        expression = expression.replace(' and ', '&&').replace(' or ', '||')
        return expression.replace('\n', '').replace('\r', '').replace(' ', '')

    def tokenize(expression):
        """ Tokenize expression into a list of tokens and operands """
        tokens = []
        current_token = None
        operand_token = None
        in_quote = False

        for char in expression:

            # protect anything in quotes from being tokenized
            if in_quote is True:
                if char == '"':
                    in_quote = False
                    tokens.append(current_token+char)
                    current_token = None
                else:
                    current_token+=char
                continue

            # catch starting quote
            if char == '"':
                in_quote = True
                if current_token is None:
                    current_token=char
                else:
                    current_token+=char
                continue

            # operands
            if char in "*/%+-?:&|=<>!()":
                # end the current token when an operand is found
                if current_token is not None:
                    tokens.append(current_token)
                    current_token = None

                # single char operands 
                if char in "*/+-?:()":
                    tokens.append(char)
                # two char operands 
                elif char in "=<>!&|":
                    # if first operand token
                    if operand_token is None:
                        operand_token = char
                        
                    # if second operand token
                    else:
                        tokens.append(operand_token+char)
                        operand_token = None
                continue

            # end the operand token when an operand is found
            if operand_token is not None:
                tokens.append(operand_token)
                operand_token = None
            
            # add the character to the current token
            if current_token is None:
                current_token=char
            else:
                current_token+=char

        #if anything is left after the string ends
        if current_token is not None:
            tokens.append(current_token)

        return tokens

    def replace_params(expression, config_dict, static_only=False):
        """ Replace tokens with values """
        # Search for all tokens and replace with the value on dictionary
        token_pattern = re.compile(r'@[A-Z]+[a-zA-Z0-9_]*')
        for index in range(len(expression)):
            if token_pattern.match(expression[index]):
                config_id = expression[index][1:]
                config_entry = config_dict.get(config_id)
                if config_entry is not None:
                    if (static_only is True) and (config_entry.is_static() is False):
                        continue
                    value = config_entry.get_value()
                else:
                    value = '0'
                expression[index] = value
        return expression

    def solve(expression):
        """ solve expression according to C precedence """

        result = EvalExpressions.solve_numbers(expression)
        result = EvalExpressions.solve_negative_numbers(result)
        result = EvalExpressions.solve_parentheses(result)
        result = EvalExpressions.solve_operands(result, ['*', '/', '%'])
        result = EvalExpressions.solve_operands(result, ['+', '-'])
        result = EvalExpressions.solve_operands(result, ['<<', '>>'])
        result = EvalExpressions.solve_operands(result, ['<', '>', '==', '<=', '>=', '!='])
        result = EvalExpressions.solve_logic(result)
        result = EvalExpressions.solve_ternary(result)

        if (len(result)==0):
            return ''
        elif (len(result)==1):
            return result[0]
        else:
            raise EvalExpressionsError("Expression could not be resolved", expression)

    def solve_numbers(expression):
        """ solve numbers in a tokenized expression """
        # solve number format
        token_hex = re.compile(r'0[xX][0-9A-Fa-f_]+')
        token_float = re.compile(r'[0-9]+\.[0-9]+')
        for index in range(len(expression)):
            if isinstance(expression[index], str) is True:
                # replace hex values as strings with integers
                if token_hex.match(expression[index]):
                    expression[index] = int(expression[index], base=16)

                # replace float values as strings with floats
                elif token_float.match(expression[index]):
                    expression[index] = float(expression[index])

                # replace numeric values as strings with integers
                elif expression[index].isnumeric() is True:
                    expression[index] = int(expression[index])

        return expression
    
    def solve_negative_numbers(expression):
        """ solve negative numbers in a tokenized expression """

        if ('-' not in expression):
            return expression

        while (True):
            negative_found=False
            for index in range(len(expression)):
                if (expression[index] == '-'):
                    # search for a minus at the start or after another operation
                    if (index == 0) or \
                        ((isinstance(expression[index-1], str) is True) and \
                        ((expression[index-1] in "*/+-?:()") or \
                        (expression[index-1] in ['==', '<=', '>=', '!=', '&&', '||']))):

                        # continue if value is not found or not a number
                        if (index >= len(expression)) or \
                            (isinstance(expression[index+1], str) is True):
                            continue

                        # replace both elements with the negative value
                        expression[index+1] = -expression[index+1]
                        expression.pop(index)

                        negative_found=True
                        break

            if negative_found is False:
                break

        return expression

    def solve_operands(expression, operands):
        """ solve the operations in a tokenized expression """

        # solve each set of operand on at a time
        while(True):
            op_found=False
            for index in range(len(expression)):
                if expression[index] in operands:
                    # locate the operand and arguments
                    operand = expression[index]
                    prev = index - 1
                    post = index + 1
                    if (prev < 0) or (post > len(expression)):
                        raise EvalExpressionsError("Invalid condition in expression", expression)

                    # mark that an operand is found
                    op_found = True

                    # validate the argument to be used
                    prev_value = expression[prev]
                    post_value = expression[post]
                    prev_unresolved = (isinstance(prev_value, str) is True) and ('@' in prev_value)
                    post_unresolved = (isinstance(post_value, str) is True) and ('@' in post_value)

                    if (prev_unresolved is True) or (post_unresolved is True):
                        # An unresolved parameter has been found
                        # Collapse all 3 elements into 1
                        expression[prev] = str(prev_value) + ' ' + operand + ' ' + str(post_value)
                        expression.pop(post)
                        expression.pop(index)
                        break

                    if (isinstance(prev_value, int) is False) or (isinstance(post_value, int) is False):
                        raise EvalExpressionsError("Invalid arguments for operand: %s" % operand, expression)

                    # evaluate the result
                    result = eval(str(prev_value) + operand + str(post_value))

                    # ensure the format of the result
                    if result is True:
                        result = 1
                    elif result is False:
                        result = 0
                    if isinstance(result, float) is True:
                        result = int(result)

                    # collapse all 3 elements into 1
                    expression[prev] = result
                    expression.pop(post)
                    expression.pop(index)
                    break

            # exit only if the whole expression contains no valid operand
            if op_found is False:
                break

        return expression

    def solve_logic(expression):
        """ solve the operations in a tokenized expression """

        # solve each set of operand on at a time
        while(True):
            op_found=False
            for index in range(len(expression)):
                if expression[index] in ['&&', '||']:
                    # locate the operand and arguments
                    operand = expression[index]
                    prev = index - 1
                    post = index + 1
                    if (prev < 0) or (post > len(expression)):
                        raise EvalExpressionsError("Invalid condition in expression", expression)

                    # mark that an operand is found
                    op_found = True

                    # validate the argument to be used
                    prev_value = expression[prev]
                    post_value = expression[post]
                    prev_unresolved = (isinstance(prev_value, str) is True) and ('@' in prev_value)
                    post_unresolved = (isinstance(post_value, str) is True) and ('@' in post_value)
                    # if resolved value must be an 0 or 1
                    if ((prev_unresolved is False) and (prev_value not in [0, 1])) or \
                       ((post_unresolved is False) and (post_value not in [0, 1])):
                        raise EvalExpressionsError("Invalid arguments for operand: %s" % operand, expression)

                    # Evaluate the result

                    # Both unresolved
                    if (prev_unresolved is True) and (post_unresolved is True):
                        result = '('+ str(prev_value) + ') ' + operand + ' (' + str(post_value) + ')'
                    # AND
                    elif operand == '&&':
                        if (prev_value == 0) or (post_value == 0):
                            result = 0
                        elif prev_unresolved is True:
                            # Replace with first term
                            result = prev_value
                        elif post_unresolved is True:
                            # Replace with second term
                            result = post_value
                        else:
                            # if both are resolved and both are 1
                            result = 1
                    # OR
                    elif operand == '||':
                        if (prev_value == 1) or (post_value == 1):
                            result = 1
                        elif prev_unresolved is True:
                            # Replace with first term
                            result = prev_value
                        elif post_unresolved is True:
                            # Replace with second term
                            result = post_value
                        else:
                            # if both are resolved and both are 0
                            result = 0

                    # collapse all 3 elements into 1
                    expression[prev] = result
                    expression.pop(post)
                    expression.pop(index)
                    break

            # exit only if the whole expression contains no valid operand
            if op_found is False:
                break

        return expression

    def solve_parentheses(expression):
        """ solve parentheses in a tokenized expression """

        # test if parentheses are found
        if '(' not in expression:
            return expression

        # before '(' inner ')' after

        # split expression with the opening parenthesis
        opening = expression.index('(')
        before = expression[:opening]
        sub_expression = expression[opening+1:]
        
        # test if closing parenthesis are found
        if ')' not in sub_expression:
            raise EvalExpressionsError("parentheses mismatch", expression)

        # solve nested parentheses
        while '(' in sub_expression:
            sub_expression = EvalExpressions.solve_parentheses(sub_expression)

        # split expression with the closing parenthesis
        closing = sub_expression.index(')')
        inner = sub_expression[:closing]
        after = sub_expression[closing+1:]

        # solve the contents of the parentheses
        result = EvalExpressions.solve(inner)
        return before + [result] + after

    def solve_ternary(expression):
        """ solve ternary conditions in a tokenized expression """

        # test if a ternary condition is found
        if '?' not in expression:
            return expression

        # before + condition '?' result_true ':' result_false + after

        # split expression with the opening delimiter
        opening = expression.index('?')
        before = expression[:opening-1]
        condition = expression[opening-1]
        results = expression[opening+1:]
        
        # test if closing delimiter are found
        if ':' not in results:
            raise EvalExpressionsError("ternary mismatch", expression)

        # solve nested ternary conditions
        while '?' in results:
            results = EvalExpressions.solve_ternary(results)

        # split expression with the closing delimiter
        closing = results.index(':')
        result_true = results[:closing]
        result_false = [results[closing+1]]
        after = results[closing+2:]

        # chose the result based on condition
        if (isinstance(condition, str) is True) and ('@' in condition):
            # condition unresolved
            result = '('+ condition + ')?' + str(result_false) + ':' + str(result_false)
        elif condition == 1:
            result = result_true
        elif condition == 0:
            result = result_false
        else:
            raise EvalExpressionsError("Ternary condition cannot be evaluated %s" % condition, expression)

        return before + result + after
