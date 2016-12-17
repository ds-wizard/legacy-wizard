-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Book" cascade;
create table "Book" (
	id serial primary key,
	chapter varchar(10) not null,
	contents text not null
);
alter table "Book" owner to elixir;

insert into "Book" (chapter, contents) values ('1.4', 'Book section 1.4 contents');
insert into "Book" (chapter, contents) values ('1.5', 'Book section 1.5 contents');
insert into "Book" (chapter, contents) values ('1.6', 'Book section 1.6 contents');

drop table "Questions" cascade;
create table "Questions" (
	chapterId int,
	questionId int,
	bookRef varchar(10) null,
	otherInfo text null,
        primary key (chapterId, questionId)
);
alter table "Questions" owner to elixir;

