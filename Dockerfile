FROM openjdk:12-alpine

RUN apk add --no-cache nodejs npm

#TODO find out why this breaks copying files
#WORKDIR /usr/chor

# expose ports
EXPOSE 3000

# install packages
COPY package*.json /
RUN npm install

# copy sources and build
COPY . /
RUN npm run build

ENTRYPOINT ["npm"]
CMD ["run", "serve"]