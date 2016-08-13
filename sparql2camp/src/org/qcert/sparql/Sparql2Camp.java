/**
 * Copyright (C) 2016 Joshua Auerbach 
 *
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
package org.qcert.sparql;

import org.apache.jena.query.Query;
import org.apache.jena.query.QueryFactory;
import org.apache.jena.query.QueryVisitor;
import org.apache.jena.sparql.core.Prologue;
import org.qcert.camp.rule.CampRule;

/**
 * Main translator from SPARQL (Jena ARQ) to CAMP (with Rules)
 */
public class Sparql2Camp implements QueryVisitor {
	private CampRule result;

	/**
	 * Convert a specific query into CAMP.  The Query can be obtained by any of the methods
	 *   provided by the Jena QueryFactory.
	 * @param query the query as an ARQ Query object
	 * @return the CAMP (outermost, a rule)
	 */
	public static final CampRule translate(Query query) {
		Sparql2Camp visitor = new Sparql2Camp();
		query.visit(visitor);
		return visitor.result;
	}
	
	/**
	 * Convenience method to convert a string-form SPARQL query, hiding the Jena ARQ details
	 *  of constructing a Query object, parsing, etc.
	 * @param query the query as a String
	 * @return the CAMP (outermost, a rule)
	 */
	public static final CampRule translate(String query) {
		return translate(QueryFactory.create(query));
	}
	
	/**
	 * Convenience method to convert a file containing a SPARQL query, hiding the Jena ARQ details
	 *  reading the file, constructing a Query object, parsing, etc.
	 * @param file the name of the file containing the SPARQL (fully qualified or relative to the current directory)
	 * @return the CAMP (outermost, a rule)
	 */
	public static final CampRule translateFile(String file) {
		return translate(QueryFactory.read(file));
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#finishVisit(org.apache.jena.query.Query)
	 */
	@Override
	public void finishVisit(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#startVisit(org.apache.jena.query.Query)
	 */
	@Override
	public void startVisit(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitAskResultForm(org.apache.jena.query.Query)
	 */
	@Override
	public void visitAskResultForm(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitConstructResultForm(org.apache.jena.query.Query)
	 */
	@Override
	public void visitConstructResultForm(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitDatasetDecl(org.apache.jena.query.Query)
	 */
	@Override
	public void visitDatasetDecl(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitDescribeResultForm(org.apache.jena.query.Query)
	 */
	@Override
	public void visitDescribeResultForm(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitGroupBy(org.apache.jena.query.Query)
	 */
	@Override
	public void visitGroupBy(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitHaving(org.apache.jena.query.Query)
	 */
	@Override
	public void visitHaving(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitLimit(org.apache.jena.query.Query)
	 */
	@Override
	public void visitLimit(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitOffset(org.apache.jena.query.Query)
	 */
	@Override
	public void visitOffset(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitOrderBy(org.apache.jena.query.Query)
	 */
	@Override
	public void visitOrderBy(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitPrologue(org.apache.jena.sparql.core.Prologue)
	 */
	@Override
	public void visitPrologue(Prologue prologue) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitQueryPattern(org.apache.jena.query.Query)
	 */
	@Override
	public void visitQueryPattern(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitResultForm(org.apache.jena.query.Query)
	 */
	@Override
	public void visitResultForm(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitSelectResultForm(org.apache.jena.query.Query)
	 */
	@Override
	public void visitSelectResultForm(Query query) {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see org.apache.jena.query.QueryVisitor#visitValues(org.apache.jena.query.Query)
	 */
	@Override
	public void visitValues(Query query) {
		// TODO Auto-generated method stub
		
	}
}
