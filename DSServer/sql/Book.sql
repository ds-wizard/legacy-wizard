-- -h localhost -U postgres -d elixir-dswizard
-- vim: syntax=pgsql:

drop table "Book" cascade;
create table "Book" (
	id serial primary key,
	chapter text not null,
	contents text not null,
	shortuid text
);
alter table "Book" owner to elixir;

insert into "Book" (chapter, contents) values ('1.4', 'Book section 1.4 contents');
insert into "Book" (chapter, contents) values ('1.5', 'Book section 1.5 contents');
insert into "Book" (chapter, contents) values ('1.6', 'Book section 1.6 contents');
