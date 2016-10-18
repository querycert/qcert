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

DAY = "DAY";
MONTH = "MONTH";
YEAR = "YEAR";

function sqlGetDateComponent(part, date) {
		mustBeDate(date);
		switch(part) {
		case DAY:
				return date.day;
		case MONTH:
				return date.month;
		case YEAR:
				return date.year;
		default:
				throw new Error("Uninterpretable part: " + part);
		}
}

function sqlDateFromString(stringDate) {
		throw new Error("We should not be seeing dates except as objects with structure");
}

function sqlDateDurationFromString(stringDuration) {
		throw new Error("We should not be seeing durations except as objects with structure");
}

function sqlDatePointPlus(date, duration) {
		mustBeDate(date);
		mustBeDuration(duration);
		switch(duration.unit) {
		case DAY:
				return dateNewDay(date, day.day + duration.duration);
		case MONTH:
				return dateNewMonth(date, day.month + duration.duration);
		case YEAR:
				return dateNewYear(date, day.year + duration.duration);
		default:
				throw new Error("Unexpected state (not supposed to happen)");
		}
}

function sqlDatePointMinus(date, duration) {
		mustBeDate(date);
		mustBeDuration(duration);
		switch(duration.unit) {
		case DAY:
				return dateNewDay(date, day.day - duration.duration);
		case MONTH:
				return dateNewMonth(date, day.month - duration.duration);
		case YEAR:
				return dateNewYear(date, day.year - duration.duration);
		default:
				throw new Error("Unexpected state (not supposed to happen)");
		}
}

function sqlDatePointNe(date1, date2) {
		mustBeDate(date1);
		mustBeDate(date2);
		return compareDates(date1, date2) != 0;
}

function sqlDatePointLt(date1, date2) {
		mustBeDate(date1);
		mustBeDate(date2);
		return compareDates(date1, date2) < 0;
}

function sqlDatePointLe(date, date2) {
		mustBeDate(date1);
		mustBeDate(date2);
		return compareDates(date1, date2) <= 0;
}

function sqlDatePointGt(date1, date2) {
		mustBeDate(date1);
		mustBeDate(date2);
		return compareDates(date1, date2) > 0;
}

function sqlDatePointGe(date1, date2) {
		mustBeDate(date1);
		mustBeDate(date2);
		return compareDates(date1, date2) >= 0;
}

function sqlDateDurationBetween(date1, date) {
		throw new Error("We don't know how to do 'duration between' dates yet");
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

function dateNewYear(date, year) {
		return {"year": year, "month": date.month, "day": date.day};
}

function dateNewMonth(date, month) {
		/* Use Javascript Date object to handle wrapping */
		var jsDate = new Date(date.year, month, date.day);
		return jsDateToOurDate(jsDate);
}

function dateNewDay(date, day) {
		/* Use Javascript Date object to handle wrapping */
		var jsDate = new Date(date.year, date.month, day);
		return jsDateToOurDate(jsDate);
}

function jsDateToOurDate(date) {
		return {"year": date.year, "month": date.month, "day": date.day};
}

function mustBeDate(date) {
		if (typeof date === "object" && "year" in date && "month" in date && "day" in date)
				return;
		throw new Error("Expected a date but got " + JSON.stringify(date));
}

function mustBeDuration(duration) {
		if (typeof duration === "object" && "duration" in duration && "unit" in duration)
				if (duration.unit === DAY || duration.unit === MONTH || duration.unit === YEAR)
						return;
		throw new Error("Expected a duration but got " + JSON.stringify(duration));
}
