#!/usr/bin/env node
/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

'use strict';

const Logger = require('../lib/logger');
const Commands = require('../lib/commands');

require('yargs')
    .scriptName('qcertRun')
    .demandCommand(1, '# Please specify a command')
    .recommendCommands()
    .strict()
    .command('execute', 'Compile and execute a query', (yargs) => {
        yargs.demandOption(['source', 'query','schema','input'], 'Please provide at least the source language, query, schema and input');
        yargs.usage('Usage: $0 execute --source [lang] --query [file] --schema [file] --input [file]');
        yargs.option('source', {
            describe: 'the source language',
            type: 'string',
        });
        yargs.option('query', {
            describe: 'the query',
            type: 'string'
        });
        yargs.option('schema', {
            describe: 'the schema',
            type: 'string'
        });
        yargs.option('input', {
            describe: 'the data',
            type: 'string'
        });
        yargs.option('output', {
            describe: 'the expected result',
            type: 'string'
        });
        yargs.option('eval-validate', {
            describe: 'check result correctness',
            type: 'boolean',
            default: false
        });
    }, (argv) => {
        let files = argv._;

        // Compile and Execute
        try {
            const result = Commands.execute(argv.source, { file: argv.schema }, argv.query, { file: argv.input }, argv.output ? { file: argv.output } : null, argv['eval-validate']);
            Logger.info(result);
        } catch(err) {
            Logger.error(err.message);
        };
    })
    .option('verbose', {
        alias: 'v',
        default: false
    })
    .argv;
