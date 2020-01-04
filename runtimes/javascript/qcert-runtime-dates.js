/*
 * Copyright 2016 Joshua Auerbach
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

/* Addendum to "standard library" with limited support for SQL-style dates and durations (aka "intervals") */

/* Utilities */
var DAY = "DAY";
var MONTH = "MONTH";
var YEAR = "YEAR";

function makeDate(year, month, day) {
    return {"year": year, "month": month, "day": day};
}

function mustBeDate(date) {
    if (typeof date === "object" && "year" in date && "month" in date && "day" in date)
	      return;
    throw "Expected a date but got " + JSON.stringify(date));
}

function mustBeDuration(duration) {
    if (typeof duration === "object" && "duration" in duration && "unit" in duration) {
	      mustBeUnit(duration.unit);
	      return;
    }
    throw "Expected a duration but got " + JSON.stringify(duration);
}

function mustBeUnit(unit) {
    if (unit === DAY || unit === MONTH || unit === YEAR)
	      return;
    throw "Expected a duration unit but got " + JSON.stringify(unit);
}

function compareDates(date1, date2) {
    if (date1.year < date2.year)
	      return -1;
    if (date1.year > date2.year)
	      return 1;
    if (date1.month < date2.month)
	      return -1;
    if (date1.month > date2.month)
	      return 1;
    if (date1.day < date2.day)
	      return -1;
    if (date1.day > date2.day)
	      return 1;
    return 0;
}

/* Date */
function dateFromString(stringDate) {
    if (typeof stringDate === "string") {
	      parts = stringDate.split("-");
	      if (parts.length === 3)
	          return makeDate(Number(parts[0]), Number(parts[1]), Number(parts[2]));
	      throw ("Malformed string date: " + stringDate);
    }
    throw ("Expected a date in string form but got " + JSON.stringify(stringDate));
}

function dateGetYear(date) {
    mustBeDate(date);
	  return date.year;
}

function dateGetMonth(date) {
    mustBeDate(date);
	  return date.month;
}

function dateGetDay(date) {
    mustBeDate(date);
	  return date.day;
}

function dateNe(date1, date2) {
    mustBeDate(date1);
    mustBeDate(date2);
    return compareDates(date1, date2) != 0;
}

function dateLt(date1, date2) {
    mustBeDate(date1);
    mustBeDate(date2);
    return compareDates(date1, date2) < 0;
}

function dateLe(date1, date2) {
    mustBeDate(date1);
    mustBeDate(date2);
    return compareDates(date1, date2) <= 0;
}

function dateGt(date1, date2) {
    mustBeDate(date1);
    mustBeDate(date2);
    return compareDates(date1, date2) > 0;
}

function dateGe(date1, date2) {
    mustBeDate(date1);
    mustBeDate(date2);
    return compareDates(date1, date2) >= 0;
}


function dateSetYear(date, year) {
    return makeDate(year, date.month, date.day);
}

function dateSetMonth(date, month) {
    /* Use Javascript Date object to normalize out-of-range month */
    var jsDate = new Date(date.year, month-1, date.day);
    return makeDate(jsDate.getFullYear(), jsDate.getMonth()+1, jsDate.getDate());
}

function dateSetDay(date, day) {
    /* Use Javascript Date object to normalize out-of-range day */
    var jsDate = new Date(date.year, date.month-1, day);
    return makeDate(jsDate.getFullYear(), jsDate.getMonth()+1, jsDate.getDate());
}

/* Duration */
function durationFromString(stringDuration) {
    // TODO verify what the string format for durations is going to be.
    // Here we assume a number adjoined to a valid unit with a dash.
    if (typeof stringDuration === "string") {
	      parts = stringDuration.split("-");
	      if (parts.length === 2) {
	          mustBeUnit(parts[1]);
	          return {"duration": Number(parts[0]), "unit": parts[1]};
	          throw ("Malformed string duration: " + stringDuration);
	      }
	      throw ("Expected a duration in string form but got " + JSON.stringify(stringDuration));
    }
}

function durationPlus(date, duration) {
    mustBeDate(date);
    mustBeDuration(duration);
    switch(duration.unit) {
    case DAY:
	      return dateNewDay(date, date.day + duration.duration);
    case MONTH:
	      return dateNewMonth(date, date.month + duration.duration);
    case YEAR:
	      return dateNewYear(date, date.year + duration.duration);
    default:
	      throw "Unexpected state (not supposed to happen)";
    }
}

function durationMinus(date, duration) {
    mustBeDate(date);
    mustBeDuration(duration);
    switch(duration.unit) {
    case DAY:
	      return dateNewDay(date, date.day - duration.duration);
    case MONTH:
	      return dateNewMonth(date, date.month - duration.duration);
    case YEAR:
	      return dateNewYear(date, date.year - duration.duration);
    default:
	      throw ("Unexpected bad unit (not supposed to happen)");
    }
}

function durationBetween(date1, date) {
    throw ("We don't know how to do 'duration between' dates yet");
}
